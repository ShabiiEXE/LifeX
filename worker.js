const PIN_LENGTH = 4;
const CREATE_ATTEMPTS = 128;
const ROOM_INDEX_NAME = "__sync-room-index__";

function json(data, init = {}) {
  return new Response(JSON.stringify(data), {
    ...init,
    headers: {
      "content-type": "application/json; charset=utf-8",
      ...(init.headers || {})
    }
  });
}

function normalizeName(value) {
  return `${value || ""}`.trim().replace(/\s+/g, " ").toLowerCase();
}

function normalizePin(value) {
  const digits = `${value || ""}`.replace(/\D/g, "").slice(0, PIN_LENGTH);
  return digits.length === PIN_LENGTH ? digits : "";
}

function normalizePassword(value) {
  const digits = `${value || ""}`.replace(/\D/g, "").slice(0, PIN_LENGTH);
  return digits.length === PIN_LENGTH ? digits : "";
}

function createEmptyRoomState(pin = "", password = "") {
  return {
    pin,
    password: normalizePassword(password),
    createdAt: Date.now(),
    updatedAt: Date.now(),
    profiles: [],
    games: [],
    historyEntries: [],
    tombstones: {
      profiles: [],
      decks: []
    },
    statsByDevice: {}
  };
}

function resetMatchDataInState(state) {
  return {
    ...state,
    updatedAt: Date.now(),
    games: [],
    historyEntries: [],
    statsByDevice: {}
  };
}

function normalizeTombstones(source) {
  const profiles = Array.isArray(source?.profiles) ? source.profiles : [];
  const decks = Array.isArray(source?.decks) ? source.decks : [];
  return {
    profiles: profiles
      .map((entry) => {
        const profileName = `${entry?.profileName || entry?.name || ""}`.trim();
        const deletedAt = Number.isFinite(entry?.deletedAt) ? entry.deletedAt : 0;
        if (!profileName || !deletedAt) return null;
        return { profileName, deletedAt };
      })
      .filter(Boolean),
    decks: decks
      .map((entry) => {
        const ownerProfileName = `${entry?.ownerProfileName || ""}`.trim();
        const commanderName = `${entry?.commanderName || entry?.name || ""}`.trim();
        const deletedAt = Number.isFinite(entry?.deletedAt) ? entry.deletedAt : 0;
        if (!ownerProfileName || !commanderName || !deletedAt) return null;
        return { ownerProfileName, commanderName, deletedAt };
      })
      .filter(Boolean)
  };
}

function mergeTombstones(existingTombstones, incomingTombstones) {
  const merged = normalizeTombstones(existingTombstones);
  const next = normalizeTombstones(incomingTombstones);

  next.profiles.forEach((entry) => {
    const existing = merged.profiles.find((current) => normalizeName(current.profileName) === normalizeName(entry.profileName));
    if (existing) {
      existing.deletedAt = Math.max(existing.deletedAt || 0, entry.deletedAt || 0);
    } else {
      merged.profiles.push(entry);
    }
  });

  next.decks.forEach((entry) => {
    const existing = merged.decks.find((current) =>
      normalizeName(current.ownerProfileName) === normalizeName(entry.ownerProfileName)
      && normalizeName(current.commanderName) === normalizeName(entry.commanderName)
    );
    if (existing) {
      existing.deletedAt = Math.max(existing.deletedAt || 0, entry.deletedAt || 0);
    } else {
      merged.decks.push(entry);
    }
  });

  return merged;
}

function getLatestProfileDeletion(profileName, tombstones) {
  return normalizeTombstones(tombstones).profiles.find((entry) =>
    normalizeName(entry.profileName) === normalizeName(profileName)
  )?.deletedAt || 0;
}

function getLatestDeckDeletion(ownerProfileName, commanderName, tombstones) {
  return normalizeTombstones(tombstones).decks.find((entry) =>
    normalizeName(entry.ownerProfileName) === normalizeName(ownerProfileName)
    && normalizeName(entry.commanderName) === normalizeName(commanderName)
  )?.deletedAt || 0;
}

function isDeletedByTombstone(deletedAt, itemTimestamp) {
  const normalizedDeletedAt = Number.isFinite(deletedAt) ? deletedAt : 0;
  const normalizedItemTimestamp = Number.isFinite(itemTimestamp) ? itemTimestamp : 0;
  if (normalizedDeletedAt <= 0) return false;
  if (normalizedItemTimestamp <= 0) return true;
  return normalizedDeletedAt >= normalizedItemTimestamp;
}

function mergeProfiles(existingProfiles = [], incomingProfiles = [], tombstones = createEmptyRoomState().tombstones) {
  const profilesByName = new Map();

  const ingestProfile = (profile) => {
    const name = `${profile?.name || ""}`.trim();
    if (!name) return;
    const profileKey = normalizeName(name);
    if (!profilesByName.has(profileKey)) {
      profilesByName.set(profileKey, {
        name,
        lastUsedAt: Number.isFinite(profile?.lastUsedAt) ? profile.lastUsedAt : 0,
        decksByCommander: new Map()
      });
    }
    const target = profilesByName.get(profileKey);
    target.lastUsedAt = Math.max(target.lastUsedAt, Number.isFinite(profile?.lastUsedAt) ? profile.lastUsedAt : 0);

    const decks = Array.isArray(profile?.decks) ? profile.decks : [];
    decks.forEach((deck) => {
      const commanderName = `${deck?.commanderName || deck?.name || ""}`.trim();
      if (!commanderName) return;
      const commanderKey = normalizeName(commanderName);
      const importedDeckName = `${deck?.deckName || commanderName}`.trim() || commanderName;
      const hasCustomDeckName = normalizeName(importedDeckName) !== commanderKey;
      const existing = target.decksByCommander.get(commanderKey);
      if (!existing) {
        target.decksByCommander.set(commanderKey, {
          name: commanderName,
          commanderName,
          deckName: importedDeckName,
          artRef: `${deck?.artRef || ""}`.trim(),
          image: `${deck?.image || ""}`.trim(),
          lastUsedAt: Number.isFinite(deck?.lastUsedAt) ? deck.lastUsedAt : 0
        });
        return;
      }
      existing.lastUsedAt = Math.max(existing.lastUsedAt, Number.isFinite(deck?.lastUsedAt) ? deck.lastUsedAt : 0);
      if (hasCustomDeckName) existing.deckName = importedDeckName;
      if (!existing.artRef && deck?.artRef) existing.artRef = `${deck.artRef}`.trim();
      if (!existing.image && deck?.image) existing.image = `${deck.image}`.trim();
    });
  };

  existingProfiles.forEach(ingestProfile);
  incomingProfiles.forEach(ingestProfile);

  return Array.from(profilesByName.values())
    .map((profile) => ({
      name: profile.name,
      lastUsedAt: profile.lastUsedAt,
      decks: Array.from(profile.decksByCommander.values())
        .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0))
        .map((deck) => ({
          name: deck.name,
          commanderName: deck.commanderName,
          deckName: deck.deckName,
          artRef: deck.artRef,
          image: deck.image,
          lastUsedAt: deck.lastUsedAt
        }))
    }))
    .filter((profile) => !isDeletedByTombstone(getLatestProfileDeletion(profile.name, tombstones), profile.lastUsedAt || 0))
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function mergeGames(existingGames = [], incomingGames = []) {
  const byKey = new Map();
  const ingestGame = (game) => {
    const sourceEntryId = `${game?.sourceEntryId || game?.id || ""}`.trim();
    if (!sourceEntryId) return;
    const current = byKey.get(sourceEntryId);
    const normalized = {
      sourceEntryId,
      endedAt: Number.isFinite(game?.endedAt) ? game.endedAt : Date.now(),
      mode: game?.mode === "magic" ? "magic" : "commander",
      playerCount: Number.isFinite(game?.playerCount) ? game.playerCount : 0,
      winnerName: `${game?.winnerName || ""}`.trim(),
      winCause: `${game?.winCause || ""}`.trim(),
      playerNames: Array.isArray(game?.playerNames) ? game.playerNames.map((name) => `${name || ""}`.trim()) : [],
      commanderNames: Array.isArray(game?.commanderNames) ? game.commanderNames.map((name) => `${name || ""}`.trim()) : [],
      commanderArtIds: Array.isArray(game?.commanderArtIds) ? game.commanderArtIds.map((id) => `${id || ""}`.trim()) : []
    };
    if (!current || normalized.endedAt >= current.endedAt) {
      byKey.set(sourceEntryId, normalized);
    }
  };
  existingGames.forEach(ingestGame);
  incomingGames.forEach(ingestGame);
  return Array.from(byKey.values()).sort((a, b) => (b.endedAt || 0) - (a.endedAt || 0));
}

function mergeHistoryEntries(existingEntries = [], incomingEntries = []) {
  const byKey = new Map();
  const shouldReplace = (current, incoming) => {
    if (!current) return true;
    const currentLogLength = Array.isArray(current?.gameLog) ? current.gameLog.length : 0;
    const incomingLogLength = Array.isArray(incoming?.gameLog) ? incoming.gameLog.length : 0;
    if (incomingLogLength !== currentLogLength) return incomingLogLength > currentLogLength;
    const currentActions = Number.isFinite(current?.actionCount) ? current.actionCount : 0;
    const incomingActions = Number.isFinite(incoming?.actionCount) ? incoming.actionCount : 0;
    if (incomingActions !== currentActions) return incomingActions > currentActions;
    return (incoming?.endedAt || 0) >= (current?.endedAt || 0);
  };
  const ingest = (entry) => {
    const sourceEntryId = `${entry?.sourceEntryId || entry?.id || ""}`.trim();
    if (!sourceEntryId) return;
    const current = byKey.get(sourceEntryId);
    if (!shouldReplace(current, entry)) return;
    byKey.set(sourceEntryId, entry);
  };
  existingEntries.forEach(ingest);
  incomingEntries.forEach(ingest);
  return Array.from(byKey.values()).sort((a, b) => (b?.endedAt || 0) - (a?.endedAt || 0));
}

function mergeRoomBundle(state, bundle) {
  const mergedTombstones = mergeTombstones(state.tombstones, bundle?.tombstones);
  const nextState = {
    ...state,
    updatedAt: Date.now(),
    profiles: mergeProfiles(state.profiles, Array.isArray(bundle?.profiles) ? bundle.profiles : [], mergedTombstones)
      .map((profile) => ({
        ...profile,
        decks: (Array.isArray(profile.decks) ? profile.decks : []).filter((deck) =>
          !isDeletedByTombstone(
            getLatestDeckDeletion(profile.name, deck.commanderName || deck.name, mergedTombstones),
            deck.lastUsedAt || 0
          )
        )
      })),
    games: mergeGames(state.games, Array.isArray(bundle?.games) ? bundle.games : []),
    historyEntries: mergeHistoryEntries(state.historyEntries, Array.isArray(bundle?.historyEntries) ? bundle.historyEntries : []),
    tombstones: mergedTombstones,
    statsByDevice: { ...(state.statsByDevice || {}) }
  };

  const incomingStats = Array.isArray(bundle?.stats) ? bundle.stats : (bundle?.stats ? [bundle.stats] : []);
  incomingStats.forEach((snapshot) => {
    const sourceDeviceId = `${snapshot?.sourceDeviceId || ""}`.trim();
    if (!sourceDeviceId) return;
    nextState.statsByDevice[sourceDeviceId] = snapshot;
  });

  return nextState;
}

function buildBundleFromState(state) {
  return {
    profiles: Array.isArray(state?.profiles) ? state.profiles : [],
    games: Array.isArray(state?.games) ? state.games : [],
    historyEntries: Array.isArray(state?.historyEntries) ? state.historyEntries : [],
    tombstones: normalizeTombstones(state?.tombstones),
    stats: Object.values(state?.statsByDevice || {})
  };
}

export class SyncRoom {
  constructor(ctx) {
    this.ctx = ctx;
  }

  async loadState() {
    const stored = await this.ctx.storage.get("state");
    return stored || createEmptyRoomState();
  }

  async saveState(state) {
    await this.ctx.storage.put("state", state);
  }

  async clearState() {
    await this.ctx.storage.deleteAll();
  }

  async loadIndexPins() {
    const stored = await this.ctx.storage.get("pins");
    return Array.isArray(stored)
      ? stored.map((pin) => normalizePin(pin)).filter(Boolean)
      : [];
  }

  async saveIndexPins(pins) {
    const normalizedPins = Array.from(new Set(
      (Array.isArray(pins) ? pins : []).map((pin) => normalizePin(pin)).filter(Boolean)
    )).sort();
    await this.ctx.storage.put("pins", normalizedPins);
  }

  async fetch(request) {
    const url = new URL(request.url);

    if (request.method === "POST" && url.pathname.endsWith("/index/add")) {
      const payload = await request.json().catch(() => null);
      const pin = normalizePin(payload?.pin);
      if (!pin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      const pins = await this.loadIndexPins();
      pins.push(pin);
      await this.saveIndexPins(pins);
      return json({ ok: true, pin });
    }

    if (request.method === "POST" && url.pathname.endsWith("/index/remove")) {
      const payload = await request.json().catch(() => null);
      const pin = normalizePin(payload?.pin);
      if (!pin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      const pins = (await this.loadIndexPins()).filter((entry) => entry !== pin);
      await this.saveIndexPins(pins);
      return json({ ok: true, pin });
    }

    if (request.method === "GET" && url.pathname.endsWith("/index/list")) {
      return json({ pins: await this.loadIndexPins() });
    }

    if (request.method === "POST" && url.pathname.endsWith("/index/clear")) {
      await this.ctx.storage.delete("pins");
      return json({ ok: true });
    }

    const requestedPin =
      normalizePin(url.searchParams.get("pin"))
      || normalizePin(url.pathname.match(/\/room\/(\d{4})\//)?.[1] || "");
    const payload = request.method === "POST"
      ? await request.json().catch(() => null)
      : null;
    const requestedPassword = normalizePassword(payload?.password);
    const state = await this.loadState();

    if (request.method === "POST" && url.pathname.endsWith("/create")) {
      if (state.pin) {
        return json({ error: "Room already exists." }, { status: 409 });
      }
      const pin = normalizePin(url.searchParams.get("pin"));
      if (!pin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      if (!requestedPassword) {
        return json({ error: "Invalid password." }, { status: 400 });
      }
      const nextState = createEmptyRoomState(pin, requestedPassword);
      await this.saveState(nextState);
      return json({ pin });
    }

    if (request.method === "POST" && url.pathname.endsWith("/ensure")) {
      if (state.pin) {
        if (!requestedPassword) {
          return json({ error: "Wrong room password." }, { status: 401 });
        }
        if (!normalizePassword(state.password)) {
          const migratedState = {
            ...state,
            password: requestedPassword,
            updatedAt: Date.now()
          };
          await this.saveState(migratedState);
          return json({ pin: migratedState.pin, created: false });
        }
        if (requestedPassword !== normalizePassword(state.password)) {
          return json({ error: "Wrong room password." }, { status: 401 });
        }
        return json({ pin: state.pin, created: false });
      }
      if (!requestedPin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      if (!requestedPassword) {
        return json({ error: "Invalid password." }, { status: 400 });
      }
      const nextState = createEmptyRoomState(requestedPin, requestedPassword);
      await this.saveState(nextState);
      return json({ pin: requestedPin, created: true });
    }

    if (request.method === "POST" && url.pathname.endsWith("/sync")) {
      if (!state.pin) {
        return json({ error: "Room not found." }, { status: 404 });
      }
      if (!requestedPassword) {
        return json({ error: "Wrong room password." }, { status: 401 });
      }
      const roomPassword = normalizePassword(state.password);
      if (!roomPassword) {
        const migratedState = {
          ...state,
          password: requestedPassword,
          updatedAt: Date.now()
        };
        const nextState = mergeRoomBundle(migratedState, payload?.bundle || {});
        await this.saveState(nextState);
        return json({
          pin: migratedState.pin,
          bundle: buildBundleFromState(nextState),
          updatedAt: nextState.updatedAt
        });
      }
      if (requestedPassword !== roomPassword) {
        return json({ error: "Wrong room password." }, { status: 401 });
      }
      const nextState = mergeRoomBundle(state, payload?.bundle || {});
      await this.saveState(nextState);
      return json({
        pin: state.pin,
        bundle: buildBundleFromState(nextState),
        updatedAt: nextState.updatedAt
      });
    }

    if (request.method === "POST" && url.pathname.endsWith("/reset-match-data")) {
      if (!state.pin) {
        return json({ error: "Room not found." }, { status: 404 });
      }
      if (!requestedPassword) {
        return json({ error: "Wrong room password." }, { status: 401 });
      }
      const roomPassword = normalizePassword(state.password);
      if (!roomPassword) {
        const migratedState = {
          ...state,
          password: requestedPassword,
          updatedAt: Date.now()
        };
        const nextState = resetMatchDataInState(migratedState);
        await this.saveState(nextState);
        return json({ ok: true, pin: nextState.pin, updatedAt: nextState.updatedAt });
      }
      if (requestedPassword !== roomPassword) {
        return json({ error: "Wrong room password." }, { status: 401 });
      }
      const nextState = resetMatchDataInState(state);
      await this.saveState(nextState);
      return json({ ok: true, pin: nextState.pin, updatedAt: nextState.updatedAt });
    }

    if (request.method === "GET" && url.pathname.endsWith("/debug")) {
      const providedSecret = `${request.headers.get("x-debug-sync-secret") || ""}`.trim();
      if (!providedSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      if (!state.pin) {
        return json({ error: "Room not found." }, { status: 404 });
      }
      return json(state);
    }

    if (request.method === "POST" && url.pathname.endsWith("/wipe")) {
      const providedSecret = `${request.headers.get("x-admin-sync-secret") || ""}`.trim();
      if (!providedSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      await this.clearState();
      return json({ ok: true, pin: requestedPin || state.pin || "" });
    }

    return json({ error: "Not found." }, { status: 404 });
  }
}

async function createRoom(env, password) {
  const normalizedPassword = normalizePassword(password);
  if (!normalizedPassword) {
    return json({ error: "Invalid password." }, { status: 400 });
  }
  for (let attempt = 0; attempt < CREATE_ATTEMPTS; attempt += 1) {
    const pin = `${Math.floor(Math.random() * 10000)}`.padStart(PIN_LENGTH, "0");
    const id = env.SYNC_ROOM.idFromName(pin);
    const stub = env.SYNC_ROOM.get(id);
    const response = await stub.fetch(`https://sync.internal/create?pin=${pin}`, {
      method: "POST",
      headers: {
        "content-type": "application/json; charset=utf-8"
      },
      body: JSON.stringify({
        password: normalizedPassword
      })
    });
    if (response.ok) {
      return json({ pin });
    }
    if (response.status !== 409) {
      return response;
    }
  }
  return json({ error: "Unable to allocate a room." }, { status: 503 });
}

async function addPinToRoomIndex(env, pin) {
  const normalizedPin = normalizePin(pin);
  if (!normalizedPin) return;
  const id = env.SYNC_ROOM.idFromName(ROOM_INDEX_NAME);
  const stub = env.SYNC_ROOM.get(id);
  await stub.fetch("https://sync.internal/index/add", {
    method: "POST",
    headers: {
      "content-type": "application/json; charset=utf-8"
    },
    body: JSON.stringify({ pin: normalizedPin })
  });
}

async function removePinFromRoomIndex(env, pin) {
  const normalizedPin = normalizePin(pin);
  if (!normalizedPin) return;
  const id = env.SYNC_ROOM.idFromName(ROOM_INDEX_NAME);
  const stub = env.SYNC_ROOM.get(id);
  await stub.fetch("https://sync.internal/index/remove", {
    method: "POST",
    headers: {
      "content-type": "application/json; charset=utf-8"
    },
    body: JSON.stringify({ pin: normalizedPin })
  });
}

async function listRoomIndexPins(env) {
  const id = env.SYNC_ROOM.idFromName(ROOM_INDEX_NAME);
  const stub = env.SYNC_ROOM.get(id);
  const response = await stub.fetch("https://sync.internal/index/list", {
    method: "GET"
  });
  if (!response.ok) return [];
  const payload = await response.json().catch(() => null);
  return Array.isArray(payload?.pins)
    ? payload.pins.map((pin) => normalizePin(pin)).filter(Boolean)
    : [];
}

async function clearRoomIndex(env) {
  const id = env.SYNC_ROOM.idFromName(ROOM_INDEX_NAME);
  const stub = env.SYNC_ROOM.get(id);
  await stub.fetch("https://sync.internal/index/clear", {
    method: "POST"
  });
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    const configuredSecret = `${env?.DEBUG_SYNC_SECRET || ""}`.trim();

    if (request.method === "POST" && url.pathname === "/api/sync/create") {
      const payload = await request.json().catch(() => null);
      const response = await createRoom(env, payload?.password);
      if (response.ok) {
        const data = await response.clone().json().catch(() => null);
        await addPinToRoomIndex(env, data?.pin);
      }
      return response;
    }

    const ensureMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/ensure$/);
    if (request.method === "POST" && ensureMatch) {
      const pin = ensureMatch[1];
      const body = await request.text();
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      const response = await stub.fetch(`https://sync.internal/room/${pin}/ensure`, {
        method: "POST",
        headers: {
          "content-type": "application/json; charset=utf-8"
        },
        body
      });
      if (response.ok) {
        const data = await response.clone().json().catch(() => null);
        if (data?.created) {
          await addPinToRoomIndex(env, pin);
        }
      }
      return response;
    }

    const syncMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/sync$/);
    if (request.method === "POST" && syncMatch) {
      const pin = syncMatch[1];
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      return stub.fetch(`https://sync.internal/room/${pin}/sync`, {
        method: "POST",
        headers: {
          "content-type": "application/json; charset=utf-8"
        },
        body: await request.text()
      });
    }

    const resetMatchDataMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/reset-match-data$/);
    if (request.method === "POST" && resetMatchDataMatch) {
      const pin = resetMatchDataMatch[1];
      const body = await request.text();
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      return stub.fetch(`https://sync.internal/room/${pin}/reset-match-data`, {
        method: "POST",
        headers: {
          "content-type": "application/json; charset=utf-8"
        },
        body
      });
    }

    const debugMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/debug$/);
    if (request.method === "GET" && debugMatch) {
      const providedSecret = `${url.searchParams.get("key") || ""}`.trim();
      if (!configuredSecret || !providedSecret || providedSecret !== configuredSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      const pin = debugMatch[1];
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      return stub.fetch(`https://sync.internal/room/${pin}/debug`, {
        method: "GET",
        headers: {
          "x-debug-sync-secret": providedSecret
        }
      });
    }

    const wipeMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/admin\/wipe$/);
    if ((request.method === "POST" || request.method === "GET") && wipeMatch) {
      const providedSecret = `${url.searchParams.get("key") || ""}`.trim();
      if (!configuredSecret || !providedSecret || providedSecret !== configuredSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      const pin = wipeMatch[1];
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      const response = await stub.fetch(`https://sync.internal/room/${pin}/wipe`, {
        method: "POST",
        headers: {
          "x-admin-sync-secret": providedSecret
        }
      });
      if (response.ok) {
        await removePinFromRoomIndex(env, pin);
      }
      return response;
    }

    if (request.method === "GET" && url.pathname === "/api/sync/admin/list-codes") {
      const providedSecret = `${url.searchParams.get("key") || ""}`.trim();
      if (!configuredSecret || !providedSecret || providedSecret !== configuredSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      const pins = await listRoomIndexPins(env);
      return json({
        ok: true,
        count: pins.length,
        pins
      });
    }

    if ((request.method === "POST" || request.method === "GET") && url.pathname === "/api/sync/admin/wipe-all") {
      const providedSecret = `${url.searchParams.get("key") || ""}`.trim();
      if (!configuredSecret || !providedSecret || providedSecret !== configuredSecret) {
        return json({ error: "Unauthorized." }, { status: 401 });
      }
      const pins = await listRoomIndexPins(env);
      const batchSize = 25;
      let cleared = 0;
      for (let index = 0; index < pins.length; index += batchSize) {
        const batch = pins.slice(index, index + batchSize);
        const results = await Promise.all(batch.map(async (pin) => {
          const id = env.SYNC_ROOM.idFromName(pin);
          const stub = env.SYNC_ROOM.get(id);
          const response = await stub.fetch(`https://sync.internal/room/${pin}/wipe`, {
            method: "POST",
            headers: {
              "x-admin-sync-secret": providedSecret
            }
          });
          return response.ok;
        }));
        cleared += results.filter(Boolean).length;
      }
      await clearRoomIndex(env);
      return json({ ok: true, cleared, indexedRooms: pins.length });
    }

    return env.ASSETS.fetch(request);
  }
};

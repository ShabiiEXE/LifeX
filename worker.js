const PIN_LENGTH = 4;
const CREATE_ATTEMPTS = 128;

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

function createEmptyRoomState(pin = "") {
  return {
    pin,
    createdAt: Date.now(),
    updatedAt: Date.now(),
    profiles: [],
    games: [],
    historyEntries: [],
    statsByDevice: {}
  };
}

function mergeProfiles(existingProfiles = [], incomingProfiles = []) {
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
  const nextState = {
    ...state,
    updatedAt: Date.now(),
    profiles: mergeProfiles(state.profiles, Array.isArray(bundle?.profiles) ? bundle.profiles : []),
    games: mergeGames(state.games, Array.isArray(bundle?.games) ? bundle.games : []),
    historyEntries: mergeHistoryEntries(state.historyEntries, Array.isArray(bundle?.historyEntries) ? bundle.historyEntries : []),
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

  async fetch(request) {
    const url = new URL(request.url);
    const requestedPin =
      normalizePin(url.searchParams.get("pin"))
      || normalizePin(url.pathname.match(/\/room\/(\d{4})\//)?.[1] || "");
    const state = await this.loadState();

    if (request.method === "POST" && url.pathname.endsWith("/create")) {
      if (state.pin) {
        return json({ error: "Room already exists." }, { status: 409 });
      }
      const pin = normalizePin(url.searchParams.get("pin"));
      if (!pin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      const nextState = createEmptyRoomState(pin);
      await this.saveState(nextState);
      return json({ pin });
    }

    if (request.method === "POST" && url.pathname.endsWith("/ensure")) {
      if (state.pin) {
        return json({ pin: state.pin, created: false });
      }
      if (!requestedPin) {
        return json({ error: "Invalid PIN." }, { status: 400 });
      }
      const nextState = createEmptyRoomState(requestedPin);
      await this.saveState(nextState);
      return json({ pin: requestedPin, created: true });
    }

    if (request.method === "POST" && url.pathname.endsWith("/sync")) {
      if (!state.pin) {
        return json({ error: "Room not found." }, { status: 404 });
      }
      const payload = await request.json().catch(() => null);
      const nextState = mergeRoomBundle(state, payload?.bundle || {});
      await this.saveState(nextState);
      return json({
        pin: state.pin,
        bundle: buildBundleFromState(nextState),
        updatedAt: nextState.updatedAt
      });
    }

    if (request.method === "GET" && url.pathname.endsWith("/debug")) {
      if (!state.pin) {
        return json({ error: "Room not found." }, { status: 404 });
      }
      return json(state);
    }

    return json({ error: "Not found." }, { status: 404 });
  }
}

async function createRoom(env) {
  for (let attempt = 0; attempt < CREATE_ATTEMPTS; attempt += 1) {
    const pin = `${Math.floor(Math.random() * 10000)}`.padStart(PIN_LENGTH, "0");
    const id = env.SYNC_ROOM.idFromName(pin);
    const stub = env.SYNC_ROOM.get(id);
    const response = await stub.fetch(`https://sync.internal/create?pin=${pin}`, { method: "POST" });
    if (response.ok) {
      return json({ pin });
    }
    if (response.status !== 409) {
      return response;
    }
  }
  return json({ error: "Unable to allocate a room." }, { status: 503 });
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);

    if (request.method === "POST" && url.pathname === "/api/sync/create") {
      return createRoom(env);
    }

    const ensureMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/ensure$/);
    if (request.method === "POST" && ensureMatch) {
      const pin = ensureMatch[1];
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      return stub.fetch(`https://sync.internal/room/${pin}/ensure`, { method: "POST" });
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

    const debugMatch = url.pathname.match(/^\/api\/sync\/(\d{4})\/debug$/);
    if (request.method === "GET" && debugMatch) {
      const pin = debugMatch[1];
      const id = env.SYNC_ROOM.idFromName(pin);
      const stub = env.SYNC_ROOM.get(id);
      return stub.fetch(`https://sync.internal/room/${pin}/debug`);
    }

    return env.ASSETS.fetch(request);
  }
};

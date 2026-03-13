/* ==========================================================================
   LifeX App Script
   Notes:
   - Keep behavior unchanged; section headers below are for maintainability.
   - Shared state/constants live first, then helpers, UI logic, and bootstrapping.
   ========================================================================== */

/* =========================
   Core Runtime State
   ========================= */
let starting_life = 40;
let selectedPlayerCount = 0;
let activePlayerIndex = 0;
let isPaused = false;
let pauseStartedAt = null;
let turnStartTime = null;
let turnInterval = null;
let turnTotalBase = 0;
let damageSourceIndex = null;
let damageTargetIndex = null;
let damageAmount = 0;
let damageSelfMode = null; 
let selectedDamageTypes = [];
let nonCombatAutoSelected = false;
let isDragging = false;
let dragStartIndex = null;
let dragStartX = 0;
let dragStartY = 0;
let isDamageMode = false;
let isGameOver = false;
let winnerIndex = null;
let undoStack = [];
const MAX_UNDO_STATES = 40;
const MAX_GAME_LOG_ENTRIES = 300;
const MAX_COMMANDER_HISTORY_ENTRIES = 100;
let turnNumber = 1;
let gameLog = [];
let lastEliminationCause = null;
let lastEliminationSelections = [];
let endGameSelectedCauses = [];
let gameMode = "commander";
let matchStats = Array.from({ length: 6 }, () => ({
  damageDealt: 0,
  commanderDamageDealt: 0,
  poisonDealt: 0,
  healingDone: 0
}));
let matchEliminations = Array.from({ length: 6 }, () => ({
  turn: null,
  cause: ""
}));
/* =========================
   Domain Constants
   ========================= */
const ENDGAME_PRIMARY_CAUSES = [
  "Combat Damage",
  "Non-Combat Damage",
  "Commander",
  "Milled",
  "Combo",
  "Wincon",
  "Poison"
];

const STORAGE_KEY = "lifeTrackerState";
const PROFILE_STORAGE_KEY = "lifeTrackerProfilesV1";
const DECK_STORAGE_KEY = "lifeTrackerDecksV1";
const MATCH_HISTORY_STORAGE_KEY = "lifeTrackerMatchHistoryV1";
const RESUME_SESSIONS_STORAGE_KEY = "lifeTrackerResumeSessionsV1";
const START_MENU_BACKDROP_STORAGE_KEY = "lifeTrackerStartMenuBackdropV1";
const DEVICE_ID_STORAGE_KEY = "lifeXDeviceIdV1";
const QR_TRANSFER_PREFIX = "LIFEX1:";
const SCRYFALL_SEARCH_TIMEOUT_MS = 3200;
const DEFAULT_PLAYER_BACKGROUND = "./img/default_back0.png";
const DEFAULT_MAGIC_PLAYER_BACKGROUNDS = [
  "./img/default_back0.png",
  "./img/default_back1.png"
];
/* =========================
   Root DOM References
   ========================= */
const game = document.getElementById("game");
const pauseBtn = document.getElementById("pause-btn");
let setupState = null;
let profileLibrary = [];
let deckLibrary = [];
let matchHistory = [];
let resumeSessions = [];
let startMenuBackdrop = null;
let scryfallSearchToken = 0;
let setupGridPreviewActive = false;
let hasStartedGame = false;
let serviceWorkerReadyPromise = null;
let exitConfirmGuardInitialized = false;
let allowExitAfterConfirm = false;
let qrScannerStream = null;
let qrScannerLoopId = null;
let qrScannerDetector = null;
let duelSeries = createDefaultDuelSeriesState();
let pendingDuelContinuation = null;

/* =========================
   Duel Series Helpers
   ========================= */

function normalizeDuelMatchLength(value) {
  return [1, 3, 5].includes(Number(value)) ? Number(value) : 1;
}

function createDefaultDuelSeriesState(matchLength = 3) {
  return {
    seriesId: createLocalId(),
    matchLength: normalizeDuelMatchLength(matchLength),
    currentGame: 1,
    wins: [0, 0],
    winners: []
  };
}

function normalizeDuelSeriesState(state) {
  const matchLength = normalizeDuelMatchLength(state?.matchLength);
  const seriesId = typeof state?.seriesId === "string" && state.seriesId.trim()
    ? state.seriesId.trim()
    : createLocalId();
  const winners = Array.isArray(state?.winners)
    ? state.winners
        .map(value => Number.isInteger(value) && value >= 0 && value <= 1 ? value : null)
        .slice(0, matchLength)
    : [];
  const wins = [0, 0];
  winners.forEach(index => {
    if (!Number.isInteger(index)) return;
    wins[index] += 1;
  });
  return {
    seriesId,
    matchLength,
    currentGame: Math.min(matchLength, Math.max(1, Number(state?.currentGame) || (winners.length + 1))),
    wins,
    winners
  };
}

function isDuelMode(mode = gameMode) {
  return mode === "magic";
}

function getCompletedDuelGamesCount() {
  return Array.isArray(duelSeries?.winners) ? duelSeries.winners.length : 0;
}

function getDuelWinsNeeded(matchLength = duelSeries?.matchLength) {
  return Math.ceil(normalizeDuelMatchLength(matchLength) / 2);
}

function getDuelSeriesWinnerIndex(state = duelSeries) {
  const normalized = normalizeDuelSeriesState(state);
  const winsNeeded = getDuelWinsNeeded(normalized.matchLength);
  if ((normalized.wins?.[0] || 0) >= winsNeeded) return 0;
  if ((normalized.wins?.[1] || 0) >= winsNeeded) return 1;
  return null;
}

function isDuelSeriesCompleteForState(state = duelSeries) {
  const normalized = normalizeDuelSeriesState(state);
  const winsNeeded = getDuelWinsNeeded(normalized.matchLength);
  const completedGames = Array.isArray(normalized.winners) ? normalized.winners.length : 0;
  return (normalized.wins?.[0] || 0) >= winsNeeded
    || (normalized.wins?.[1] || 0) >= winsNeeded
    || completedGames >= normalized.matchLength;
}

function getProjectedDuelSeriesState(currentGameWinnerIndex = winnerIndex) {
  return normalizeDuelSeriesState({
    ...duelSeries,
    currentGame: Math.min(duelSeries.matchLength, duelSeries.currentGame),
    winners: [...(Array.isArray(duelSeries.winners) ? duelSeries.winners : []), Number.isInteger(currentGameWinnerIndex) ? currentGameWinnerIndex : null]
      .slice(0, duelSeries.matchLength)
  });
}

function isDuelSeriesComplete() {
  return isDuelMode() && isDuelSeriesCompleteForState(duelSeries);
}

function isCurrentDuelGameFinal() {
  if (!isDuelMode()) return false;
  return isDuelSeriesCompleteForState(getProjectedDuelSeriesState(winnerIndex));
}

function resetDuelSeriesState(matchLength = 1) {
  duelSeries = createDefaultDuelSeriesState(matchLength);
}

/* =========================
   UI Asset / Icon Helpers
   ========================= */
const INLINE_ICON_MARKUP = {
  Cancel: `<svg viewBox="0 0 1735.39 1735.4" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1689.28,1466.63c61.48,61.48,61.48,161.17,0,222.65-30.75,30.75-71.04,46.12-111.33,46.12s-80.58-15.37-111.32-46.12l-598.93-598.93-598.94,598.93c-61.48,61.49-161.17,61.49-222.65,0-30.74-30.74-46.11-71.03-46.11-111.33s15.37-80.58,46.11-111.32l598.93-598.93L46.11,268.77c-61.48-61.49-61.48-161.17,0-222.66C76.85,15.37,117.14,0,157.43,0s80.59,15.37,111.33,46.11l598.94,598.94L1466.63,46.11c61.48-61.48,161.16-61.48,222.65,0,30.74,30.74,46.11,71.04,46.11,111.33s-15.37,80.59-46.11,111.33l-598.93,598.93,598.93,598.93Z"/></svg>`,
  Monarch: `<svg viewBox="0 0 2446.54 1706.11" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M281.15,1503.98h1884.24c37.94,0,66.57,34.43,59.66,71.73l-10.49,56.6c-7.92,42.77-45.23,73.8-88.73,73.8H320.7c-43.5,0-80.8-31.03-88.73-73.8l-10.49-56.6c-6.91-37.3,21.72-71.73,59.66-71.73Z"/><path fill="currentColor" d="M2445.24,387.11l-159.32,860.02c-8.29,44.73-47.3,77.18-92.79,77.18H253.41c-45.49,0-84.5-32.45-92.79-77.18L1.3,387.11c-12.65-68.27,70.07-112.27,119.61-63.63l469.86,461.29c49.72,48.82,132.26,36.95,166.22-23.9L1161.24,36.42c27.1-48.56,96.96-48.56,124.06,0l404.25,724.45c33.96,60.85,116.5,72.72,166.22,23.9l469.86-461.29c49.54-48.64,132.26-4.64,119.61,63.63Z"/></svg>`,
  Ok: `<svg viewBox="0 0 2029.21 2029.21" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1014.6,0C454.25,0,0,454.25,0,1014.6s454.25,1014.61,1014.6,1014.61,1014.61-454.26,1014.61-1014.61S1574.95,0,1014.6,0ZM1014.6,1664.59c-358.97,0-649.98-291.01-649.98-649.99S655.63,364.62,1014.6,364.62s649.98,291.01,649.98,649.98-291,649.99-649.98,649.99Z"/></svg>`,
  Play: `<svg viewBox="0 0 1481.73 1698.19" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1389.8,1011.15L285.67,1671.15C159.83,1746.38,0,1655.71,0,1509.1V189.09C0,42.48,159.83-48.19,285.67,27.04l1104.13,660c122.57,73.27,122.57,250.84,0,324.11Z"/></svg>`,
  QR: `<svg viewBox="0 0 2663.47 2659.05" class="icon-img" aria-hidden="true" focusable="false"><g fill="currentColor"><path d="M597.62 1739.56H322.83C144.8 1739.56.48 1883.88.48 2061.91v274.79c0 178.03 144.32 322.35 322.35 322.35h274.79c178.03 0 322.35-144.32 322.35-322.35v-274.79c0-178.03-144.32-322.35-322.35-322.35Zm73.98 546.94c0 68.58-55.6 124.18-124.18 124.18H373.03c-68.58 0-124.18-55.6-124.18-124.18v-174.39c0-68.58 55.6-124.18 124.18-124.18h174.39c68.58 0 124.18 55.6 124.18 124.18v174.39Z"/><rect x="1700.26" y="1693.28" width="1601.58" height="319.35" rx="159.68" ry="159.68" transform="rotate(-90 2501.05 1852.955)"/><rect x="0" y="1126.53" width="2088.83" height="319.35" rx="159.68" ry="159.68"/><rect x="1219.55" y="2339.3" width="865.55" height="319.35" rx="159.68" ry="159.68"/><rect x="1219.55" y="1747.45" width="865.55" height="319.35" rx="159.68" ry="159.68"/><rect x="897.2" y="273.1" width="865.55" height="319.35" rx="159.68" ry="159.68" transform="rotate(-90 1329.975 432.775)"/><path d="M597.34 4.94H322.55C144.52 4.94.2 149.26.2 327.29v274.79c0 178.03 144.32 322.35 322.35 322.35h274.79c178.03 0 322.35-144.32 322.35-322.35V327.29c0-178.03-144.32-322.35-322.35-322.35Zm73.98 546.94c0 68.58-55.6 124.18-124.18 124.18H372.75c-68.58 0-124.18-55.6-124.18-124.18V377.49c0-68.58 55.6-124.18 124.18-124.18h174.39c68.58 0 124.18 55.6 124.18 124.18v174.39Z"/><path d="M2341.12 4.94h-274.79c-178.03 0-322.35 144.32-322.35 322.35v274.79c0 178.03 144.32 322.35 322.35 322.35h274.79c178.03 0 322.35-144.32 322.35-322.35V327.29c0-178.03-144.32-322.35-322.35-322.35Zm73.98 546.94c0 68.58-55.6 124.18-124.18 124.18h-174.39c-68.58 0-124.18-55.6-124.18-124.18V377.49c0-68.58 55.6-124.18 124.18-124.18h174.39c68.58 0 124.18 55.6 124.18 124.18v174.39Z"/></g></svg>`
};

function getIconMarkup(iconName, extraClass = "btn-icon") {
  const inlineMarkup = INLINE_ICON_MARKUP[iconName];
  if (inlineMarkup) {
    return inlineMarkup.replace('class="icon-img"', `class="${extraClass} icon-img"`);
  }
  return `<img src="./icons/${iconName}.svg" class="${extraClass} icon-img" alt="">`;
}

function isJudyPlayerName(name) {
  return (name || "").trim().toLowerCase() === "judy";
}

function getRootCssVar(name) {
  const value = getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  return value;
}

function applyJudyThemeVars(el) {
  if (!el) return;
  el.style.setProperty("--main-color", getRootCssVar("--judy-color"));
  el.style.setProperty("--main-color-alt", getRootCssVar("--judy-color-alt"));
  el.style.setProperty("--arrow-color", getRootCssVar("--judy-arrow-color"));
}

function getPlayerArrowColor(index) {
  return isJudyPlayerName(players[index]?.name)
    ? getRootCssVar("--judy-arrow-color")
    : getRootCssVar("--arrow-color");
}

function getDefaultPlayerBackground(index, mode = gameMode) {
  if (mode === "magic") {
    return DEFAULT_MAGIC_PLAYER_BACKGROUNDS[index] || DEFAULT_MAGIC_PLAYER_BACKGROUNDS[0];
  }
  return DEFAULT_PLAYER_BACKGROUND;
}

function getSeatBackgroundImage(seat, index, mode = gameMode) {
  if (mode === "magic") {
    return getDefaultPlayerBackground(index, "magic");
  }
  const image = typeof seat?.image === "string" ? seat.image.trim() : "";
  return image || getDefaultPlayerBackground(index, "commander");
}

function setPauseButtonIcon(isPausedState) {
  if (!pauseBtn) return;
  pauseBtn.innerHTML = getIconMarkup(isPausedState ? "Play" : "Pause");
}

const HAPTIC_PATTERNS = {
  minimal: 6,
  tap: 10,
  step: 16,
  success: [18, 24, 18],
  alert: [36, 18, 36]
};

function triggerHaptic(pattern = "tap") {
  if (typeof navigator === "undefined" || typeof navigator.vibrate !== "function") return false;
  const resolvedPattern = HAPTIC_PATTERNS[pattern] ?? pattern;
  if (!resolvedPattern) return false;

  try {
    return navigator.vibrate(resolvedPattern);
  } catch {
    return false;
  }
}


/* =========================
   Player Model / Defaults
   ========================= */
const players = [
  { id: 1, 
    life: starting_life, 
    name: "Player 1", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(0, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
  { id: 2, 
    life: starting_life, 
    name: "Player 2", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(1, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
  { id: 3, 
    life: starting_life, 
    name: "Player 3", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(2, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
  { id: 4, 
    life: starting_life, 
    name: "Player 4", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(3, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
  { id: 5, 
    life: starting_life, 
    name: "Player 5", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(4, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
  { id: 6, 
    life: starting_life, 
    name: "Player 6", 
    commander: "", 
    commanderArtId: "",
    image: getDefaultPlayerBackground(5, "commander"),
    poison: 0,
    commanderDamage: {},
    monarch: false
  },
];

/* =========================
   Generic Utility Helpers
   ========================= */
function safeJsonParse(raw, fallback) {
  if (!raw) return fallback;
  try {
    return JSON.parse(raw);
  } catch {
    return fallback;
  }
}

function createLocalId() {
  return `${Date.now()}-${Math.random().toString(16).slice(2, 8)}`;
}

function getOrCreateDeviceId() {
  const stored = `${localStorage.getItem(DEVICE_ID_STORAGE_KEY) || ""}`.trim();
  if (stored) return stored;
  const nextId = (window.crypto && typeof window.crypto.randomUUID === "function")
    ? window.crypto.randomUUID()
    : `lifex-${createLocalId()}-${Math.random().toString(16).slice(2, 10)}`;
  localStorage.setItem(DEVICE_ID_STORAGE_KEY, nextId);
  return nextId;
}

function toBase64Utf8(value) {
  const bytes = new TextEncoder().encode(`${value || ""}`);
  let binary = "";
  bytes.forEach(byte => {
    binary += String.fromCharCode(byte);
  });
  return btoa(binary);
}

function fromBase64Utf8(value) {
  const normalized = `${value || ""}`.trim();
  const binary = atob(normalized);
  const bytes = Uint8Array.from(binary, ch => ch.charCodeAt(0));
  return new TextDecoder().decode(bytes);
}

function createDefaultMatchStat() {
  return {
    damageDealt: 0,
    commanderDamageDealt: 0,
    poisonDealt: 0,
    healingDone: 0
  };
}

function createDefaultMatchStats() {
  return Array.from({ length: 6 }, () => createDefaultMatchStat());
}

function normalizeMatchStat(stat) {
  return {
    damageDealt: Number.isFinite(stat?.damageDealt) ? stat.damageDealt : 0,
    commanderDamageDealt: Number.isFinite(stat?.commanderDamageDealt) ? stat.commanderDamageDealt : 0,
    poisonDealt: Number.isFinite(stat?.poisonDealt) ? stat.poisonDealt : 0,
    healingDone: Number.isFinite(stat?.healingDone) ? stat.healingDone : 0
  };
}

function resetMatchStats() {
  matchStats = createDefaultMatchStats();
  matchEliminations = Array.from({ length: 6 }, () => ({
    turn: null,
    cause: ""
  }));
}

/* =========================
   Storage / Persistence
   ========================= */
const deviceId = getOrCreateDeviceId();

function loadProfileLibrary() {
  const parsed = safeJsonParse(localStorage.getItem(PROFILE_STORAGE_KEY), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(item => item && typeof item.id === "string" && typeof item.name === "string")
    .map(item => ({
      ...item,
      lastUsedAt: Number.isFinite(item.lastUsedAt) ? item.lastUsedAt : 0
    }))
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function saveProfileLibrary() {
  localStorage.setItem(PROFILE_STORAGE_KEY, JSON.stringify(profileLibrary));
}

function markProfileAsUsed(profileId) {
  if (!profileId) return null;
  const profile = profileLibrary.find(item => item.id === profileId);
  if (!profile) return null;
  profile.lastUsedAt = Date.now();
  profileLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
  saveProfileLibrary();
  return profile;
}

function loadDeckLibrary() {
  const parsed = safeJsonParse(localStorage.getItem(DECK_STORAGE_KEY), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(item => item && typeof item.id === "string" && typeof item.cardName === "string")
    .map(item => ({
      ...item,
      ownerProfileId: typeof item.ownerProfileId === "string" ? item.ownerProfileId : "",
      artId: typeof item.artId === "string" ? item.artId : "",
      artRef: typeof item.artRef === "string" ? item.artRef : "",
      lastUsedAt: Number.isFinite(item.lastUsedAt) ? item.lastUsedAt : 0
    }))
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function saveDeckLibrary() {
  localStorage.setItem(DECK_STORAGE_KEY, JSON.stringify(deckLibrary));
  warmCommanderImageCache();
}

function isCacheableCommanderImageUrl(url) {
  return /^https?:\/\//i.test(`${url || ""}`.trim());
}

function getCommanderImageUrlsToCache() {
  return Array.from(new Set(
    deckLibrary
      .map(deck => `${deck?.image || ""}`.trim())
      .filter(isCacheableCommanderImageUrl)
  ));
}

/* =========================
   Service Worker / Image Cache
   ========================= */
async function ensureServiceWorkerReady() {
  if (!("serviceWorker" in navigator)) return null;
  if (!serviceWorkerReadyPromise) {
    serviceWorkerReadyPromise = navigator.serviceWorker.register("./sw.js")
      .then(async (registration) => {
        await registration.update().catch(() => {});
        return navigator.serviceWorker.ready;
      })
      .catch(() => null);
  }
  return serviceWorkerReadyPromise;
}

async function warmCommanderImageCache() {
  const urls = getCommanderImageUrlsToCache();
  if (!urls.length || !("serviceWorker" in navigator)) return;
  await warmCommanderImageCacheUrls(urls);
}

async function warmCommanderImageCacheUrls(urls) {
  const normalizedUrls = Array.from(new Set(
    (Array.isArray(urls) ? urls : [])
      .map(url => `${url || ""}`.trim())
      .filter(isCacheableCommanderImageUrl)
  ));
  if (!normalizedUrls.length || !("serviceWorker" in navigator)) return;
  const registration = await ensureServiceWorkerReady();
  const target = registration?.active || registration?.waiting || registration?.installing || navigator.serviceWorker.controller;
  if (!target) return;
  target.postMessage({
    type: "CACHE_IMAGES",
    urls: normalizedUrls
  });
}

/* =========================
   Match History Normalization
   ========================= */
function trimMatchHistoryByCommanderCap(entries) {
  const source = Array.isArray(entries) ? entries : [];
  let commanderCount = 0;
  return source.filter((entry) => {
    if ((entry?.mode || "commander") !== "commander") return true;
    commanderCount += 1;
    return commanderCount <= MAX_COMMANDER_HISTORY_ENTRIES;
  });
}

function normalizeMatchHistoryEntry(entry) {
  if (!entry || typeof entry !== "object") return null;
  if (!Array.isArray(entry.players)) return null;
  const sourceEntryId = typeof entry.sourceEntryId === "string" && entry.sourceEntryId.trim()
    ? entry.sourceEntryId.trim()
    : (typeof entry.id === "string" ? entry.id : createLocalId());
  const createdByDeviceId = typeof entry.createdByDeviceId === "string" && entry.createdByDeviceId.trim()
    ? entry.createdByDeviceId.trim()
    : (typeof entry.sourceDeviceId === "string" ? entry.sourceDeviceId.trim() : "");

  return {
    ...entry,
    id: typeof entry.id === "string" && entry.id.trim() ? entry.id : createLocalId(),
    sourceEntryId,
    createdByDeviceId
  };
}

function loadMatchHistory() {
  const parsed = safeJsonParse(localStorage.getItem(MATCH_HISTORY_STORAGE_KEY), []);
  if (!Array.isArray(parsed)) return [];
  return trimMatchHistoryByCommanderCap(parsed.map(normalizeMatchHistoryEntry).filter(Boolean));
}

function saveMatchHistory() {
  matchHistory = trimMatchHistoryByCommanderCap(matchHistory);
  localStorage.setItem(MATCH_HISTORY_STORAGE_KEY, JSON.stringify(matchHistory));
}

function loadResumeSessions() {
  const parsed = safeJsonParse(localStorage.getItem(RESUME_SESSIONS_STORAGE_KEY), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(entry => entry && typeof entry.id === "string" && entry.snapshot?.hasStartedGame)
    .slice(0, 3);
}

function saveResumeSessions() {
  localStorage.setItem(RESUME_SESSIONS_STORAGE_KEY, JSON.stringify(resumeSessions.slice(0, 3)));
}

function saveCurrentResumeSession(snapshot) {
  if (!snapshot?.hasStartedGame || snapshot.isGameOver) return;
  const entry = {
    id: "latest-in-progress",
    savedAt: Date.now(),
    snapshot
  };
  resumeSessions = [entry];
  saveResumeSessions();
}

function clearResumeSessions() {
  resumeSessions = [];
  localStorage.removeItem(RESUME_SESSIONS_STORAGE_KEY);
}

function buildStartMenuBackdropFromSnapshot(snapshot) {
  if (!snapshot || !Array.isArray(snapshot.players)) return null;
  const count = Math.min(6, Math.max(0, snapshot.selectedPlayerCount || snapshot.players.length || 0));
  if (!count) return null;

  const playersForBackdrop = snapshot.players
    .slice(0, count)
    .map((player, index) => ({
      name: (player?.name || "").trim() || `Player ${index + 1}`,
      image: (player?.image || "").trim() || getDefaultPlayerBackground(index, snapshot.gameMode)
    }))
    .filter(player => !!player.image);

  if (!playersForBackdrop.length) return null;

  return {
    selectedPlayerCount: count,
    players: playersForBackdrop
  };
}

function loadStartMenuBackdrop() {
  return buildStartMenuBackdropFromSnapshot(
    safeJsonParse(localStorage.getItem(START_MENU_BACKDROP_STORAGE_KEY), null)
  );
}

function saveStartMenuBackdrop(snapshot) {
  const backdrop = buildStartMenuBackdropFromSnapshot(snapshot);
  if (!backdrop) return;
  startMenuBackdrop = backdrop;
  localStorage.setItem(START_MENU_BACKDROP_STORAGE_KEY, JSON.stringify(backdrop));
}

function getPreferredStartMenuBackdrop() {
  if (hasStartedGame && selectedPlayerCount > 0) {
    return buildStartMenuBackdropFromSnapshot(getCurrentStateSnapshot());
  }

  if (resumeSessions.length > 0) {
    return buildStartMenuBackdropFromSnapshot(resumeSessions[0].snapshot);
  }

  if (startMenuBackdrop) {
    return startMenuBackdrop;
  }

  const lastHistoryEntry = matchHistory[0];
  if (lastHistoryEntry?.players?.length) {
    return {
      selectedPlayerCount: lastHistoryEntry.players.length,
      players: lastHistoryEntry.players.map((player, index) => ({
        name: (player?.name || "").trim() || `Player ${index + 1}`,
        image: (player?.image || "").trim() || getDefaultPlayerBackground(index, lastHistoryEntry.mode)
      }))
    };
  }

  return null;
}

function renderStartScreenBackdrop() {
  const startScreenBg = document.getElementById("start-screen-bg");
  if (!startScreenBg) return;

  const state = ensureSetupState();
  const isHomeConfigScreen = state.step === "config" && !hasStartedGame && selectedPlayerCount === 0;
  const shouldShowBackdrop = isHomeConfigScreen;
  const backdrop = shouldShowBackdrop ? getPreferredStartMenuBackdrop() : null;

  if (!backdrop?.players?.length) {
    startScreenBg.classList.add("hidden");
    startScreenBg.innerHTML = "";
    return;
  }

  const tiles = backdrop.players.slice(0, 4);
  const filledTiles = Array.from({ length: 4 }, (_, index) => tiles[index % tiles.length]);
  startScreenBg.innerHTML = filledTiles.map(tile => `
    <div class="start-screen-bg-tile" style="background-image:url('${escapeHtml(tile.image).replace(/'/g, "\\'")}')"></div>
  `).join("");
  startScreenBg.classList.remove("hidden");
}

function getDefaultSeatState(index) {
  return {
    profileId: "",
    profileName: `Player ${index + 1}`,
    deckId: "",
    deckName: "",
    cardName: "",
    artId: "",
    borrowedFromProfileId: "",
    borrowedFromProfileName: "",
    image: getDefaultPlayerBackground(index, "commander"),
    isAddingProfile: false,
    newProfileName: "",
    hasDuplicateProfileName: false,
    isDeletingProfile: false,
    isAddingDeck: false,
    isDeletingDeck: false,
    isBorrowingDeck: false,
    borrowProfileId: "",
    searchQuery: "",
    searchResults: [],
    pendingSearchCard: null,
    searchArtOptions: [],
    isLoadingArtOptions: false
  };
}

function createDefaultSetupState() {
  return {
    step: "config",
    mode: "commander",
    playerCount: 4,
    matchLength: 3,
    startingLife: 40,
    startingPlayerIndex: 0,
    showStarterPicker: false,
    forceDeckSelection: false,
    historyView: "list",
    historyEntryId: "",
    historyDeleteMode: false,
    qrOpen: false,
    qrView: "menu",
    qrStatus: "",
    qrInput: "",
    qrDisplayPayload: "",
    qrSharePayload: "",
    qrImageUrl: "",
    seats: Array.from({ length: 6 }, (_, index) => getDefaultSeatState(index))
  };
}

function resetSetupState() {
  setupState = createDefaultSetupState();
}

function ensureSetupState() {
  if (!setupState) setupState = createDefaultSetupState();
  return setupState;
}

function modeLabel(mode) {
  return mode === "magic" ? "Duel" : "Commander";
}

function normalizeLibraryName(value) {
  return `${value || ""}`.trim().toLowerCase();
}

function isProfileSelectedInOtherSeat(state, profileId, excludeSeatIndex = -1) {
  if (!state || !profileId) return false;
  return Array.from({ length: state.playerCount }, (_, index) => index)
    .some(index => index !== excludeSeatIndex && state.seats[index]?.profileId === profileId);
}

function profileNameExists(name) {
  const normalizedName = normalizeLibraryName(name);
  if (!normalizedName) return false;
  return profileLibrary.some(profile => normalizeLibraryName(profile.name) === normalizedName);
}

function profileAlreadyHasDeck(profileId, commanderName, excludeDeckId = "") {
  const normalizedCommander = normalizeLibraryName(commanderName);
  if (!profileId || !normalizedCommander) return false;
  return deckLibrary.some(deck =>
    deck.id !== excludeDeckId &&
    deck.ownerProfileId === profileId &&
    normalizeLibraryName(deck.cardName || deck.deckName) === normalizedCommander
  );
}

function isDeckSelectedInOtherSeat(state, deckId, excludeSeatIndex = -1) {
  if (!state || !deckId) return false;
  return Array.from({ length: state.playerCount }, (_, index) => index)
    .some(index => index !== excludeSeatIndex && state.seats[index]?.deckId === deckId);
}

function getDecksForProfile(profileId) {
  if (!profileId) return [];
  return deckLibrary
    .filter(deck => deck.ownerProfileId === profileId)
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function markDeckAsUsed(deckId) {
  if (!deckId) return null;
  const deck = deckLibrary.find(item => item.id === deckId);
  if (!deck) return null;
  deck.lastUsedAt = Date.now();
  deckLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
  saveDeckLibrary();
  return deck;
}

function clearSeatDeckSelection(seat) {
  if (!seat) return;
  seat.deckId = "";
  seat.deckName = "";
  seat.cardName = "";
  seat.artId = "";
  seat.borrowedFromProfileId = "";
  seat.borrowedFromProfileName = "";
  seat.image = DEFAULT_PLAYER_BACKGROUND;
  seat.isAddingDeck = false;
  seat.isDeletingDeck = false;
  seat.isBorrowingDeck = false;
  seat.borrowProfileId = "";
  seat.searchQuery = "";
  seat.searchResults = [];
  seat.pendingSearchCard = null;
  seat.searchArtOptions = [];
  seat.isLoadingArtOptions = false;
}

function getSeatDeckLabel(seat) {
  if (!seat) return "";
  const baseName = (seat.deckName || seat.cardName || "").trim();
  if (!baseName) return "";
  const lenderName = (seat.borrowedFromProfileName || "").trim();
  return lenderName ? `${baseName} (${lenderName})` : baseName;
}

function deleteDeckById(deckId) {
  if (!deckId) return false;
  const index = deckLibrary.findIndex(item => item.id === deckId);
  if (index === -1) return false;
  deckLibrary.splice(index, 1);
  saveDeckLibrary();

  if (setupState?.seats) {
    setupState.seats.forEach((seat) => {
      if (seat?.deckId === deckId) {
        clearSeatDeckSelection(seat);
      }
    });
  }

  return true;
}

function deleteProfileById(profileId) {
  if (!profileId) return false;
  const profileIndex = profileLibrary.findIndex(item => item.id === profileId);
  if (profileIndex === -1) return false;
  profileLibrary.splice(profileIndex, 1);
  saveProfileLibrary();

  deckLibrary = deckLibrary.filter(deck => deck.ownerProfileId !== profileId);
  saveDeckLibrary();

  if (setupState?.seats) {
    setupState.seats.forEach((seat, index) => {
      if (seat?.profileId === profileId) {
        const fallback = getDefaultSeatState(index);
        seat.profileId = "";
        seat.profileName = fallback.profileName;
        seat.isAddingProfile = false;
        seat.newProfileName = "";
        seat.isDeletingProfile = false;
        clearSeatDeckSelection(seat);
      }
    });
  }

  return true;
}

function isCommanderEligibleCard(card) {
  if (!card) return false;
  const isCommanderLegal = `${card.legalities?.commander || ""}`.toLowerCase() === "legal";
  if (!isCommanderLegal) return false;

  const cardTypeLine = `${card.type_line || ""}`.toLowerCase();
  const cardOracle = `${card.oracle_text || ""}`.toLowerCase();

  const hasLegendaryCreatureType =
    cardTypeLine.includes("legendary") &&
    cardTypeLine.includes("creature");
  const hasLegendarySpacecraftType =
    cardTypeLine.includes("legendary") &&
    cardTypeLine.includes("spacecraft");

  const hasCanBeCommanderText = cardOracle.includes("can be your commander");

  const faceData = Array.isArray(card.card_faces) ? card.card_faces : [];
  const hasFaceLegendaryCreatureType = faceData.some((face) => {
    const typeLine = `${face?.type_line || ""}`.toLowerCase();
    return typeLine.includes("legendary") && typeLine.includes("creature");
  });
  const hasFaceLegendarySpacecraftType = faceData.some((face) => {
    const typeLine = `${face?.type_line || ""}`.toLowerCase();
    return typeLine.includes("legendary") && typeLine.includes("spacecraft");
  });
  const hasFaceCommanderText = faceData.some((face) =>
    `${face?.oracle_text || ""}`.toLowerCase().includes("can be your commander")
  );

  return (
    hasLegendaryCreatureType ||
    hasLegendarySpacecraftType ||
    hasCanBeCommanderText ||
    hasFaceLegendaryCreatureType ||
    hasFaceLegendarySpacecraftType ||
    hasFaceCommanderText
  );
}

function getCardArtCrop(card) {
  if (!card) return "";
  if (card.image_uris?.art_crop) return card.image_uris.art_crop;
  if (Array.isArray(card.card_faces)) {
    for (const face of card.card_faces) {
      if (face?.image_uris?.art_crop) return face.image_uris.art_crop;
    }
  }
  return "";
}

function scoreCommanderSearchResult(query, card) {
  const cleanQuery = (query || "").trim().toLowerCase();
  const name = `${card?.name || ""}`.toLowerCase();
  const typeLine = `${card?.type_line || ""}`.toLowerCase();
  if (!cleanQuery || !name) return 0;

  let score = 0;
  if (name === cleanQuery) score += 1000;
  if (name.startsWith(cleanQuery)) score += 500;
  if (name.includes(cleanQuery)) score += 180;

  cleanQuery.split(/\s+/).filter(Boolean).forEach((word, index) => {
    if (name.includes(word)) score += Math.max(50 - (index * 4), 20);
    if (typeLine.includes(word)) score += 8;
  });

  return score;
}

/* =========================
   Snapshot Save / Load
   ========================= */
function saveState() {
  if (!hasStartedGame || setupGridPreviewActive || selectedPlayerCount === 0) {
    localStorage.removeItem(STORAGE_KEY);
    return;
  }

  syncActivePlayerTimer();

  const state = {
    hasStartedGame,
    gameMode,
    duelSeries,
    starting_life,
    selectedPlayerCount,
    activePlayerIndex,
    isPaused,
    isGameOver,
    winnerIndex,
    turnNumber,
    gameLog,
    lastEliminationCause,
    lastEliminationSelections,
    endGameSelectedCauses,
    matchStats,
    matchEliminations,
    undoStack,
    players: players.map(p => ({
      life: p.life,
      name: p.name || "",
      commander: p.commander || "",
      commanderArtId: p.commanderArtId || "",
      image: p.image || "",
      totalTime: p.totalTime || 0,
      turnTime: p.turnTime || 0,
      poison: p.poison || 0,
      commanderDamage: p.commanderDamage || {},
      monarch: !!p.monarch
    }))
  };

  localStorage.setItem(STORAGE_KEY, JSON.stringify(state));
  saveCurrentResumeSession(state);
  saveStartMenuBackdrop(state);
}

function loadState() {
  const saved = localStorage.getItem(STORAGE_KEY);
  if (!saved) return false;

  let state = null;
  try {
    state = JSON.parse(saved);
  } catch {
    localStorage.removeItem(STORAGE_KEY);
    return false;
  }

  if (!state?.hasStartedGame) {
    localStorage.removeItem(STORAGE_KEY);
    return false;
  }

  hasStartedGame = true;

  gameMode = state.gameMode === "magic" ? "magic" : "commander";
  duelSeries = normalizeDuelSeriesState(state.duelSeries);
  starting_life = Number.isFinite(state.starting_life) ? state.starting_life : 40;
  selectedPlayerCount = Math.min(6, Math.max(2, state.selectedPlayerCount || 4));
  activePlayerIndex = Math.min(selectedPlayerCount - 1, Math.max(0, state.activePlayerIndex || 0));
  isPaused = state.isPaused || false;
  isGameOver = state.isGameOver || false;
  winnerIndex = state.winnerIndex ?? null;
  turnNumber = Number.isFinite(state.turnNumber) && state.turnNumber > 0 ? state.turnNumber : 1;
  gameLog = Array.isArray(state.gameLog) ? state.gameLog : [];
  lastEliminationCause = state.lastEliminationCause || null;
  matchStats = Array.isArray(state.matchStats)
    ? Array.from({ length: 6 }, (_, i) => normalizeMatchStat(state.matchStats[i]))
    : createDefaultMatchStats();
  matchEliminations = Array.isArray(state.matchEliminations)
    ? Array.from({ length: 6 }, (_, i) => ({
      turn: Number.isFinite(state.matchEliminations[i]?.turn) ? state.matchEliminations[i].turn : null,
      cause: state.matchEliminations[i]?.cause || ""
    }))
    : Array.from({ length: 6 }, () => ({ turn: null, cause: "" }));
  lastEliminationSelections = Array.isArray(state.lastEliminationSelections) ? [...state.lastEliminationSelections] : [];
  if (Array.isArray(state.endGameSelectedCauses)) {
    endGameSelectedCauses = [...state.endGameSelectedCauses];
  } else {
    // Backward compatibility with previous endgame state format.
    endGameSelectedCauses = [];
    if (state.endGameSelectedCause) endGameSelectedCauses.push(state.endGameSelectedCause);
    if (state.endGameComboSelected) endGameSelectedCauses.push("Combo");
  }
  undoStack = Array.isArray(state.undoStack) ? state.undoStack : [];

  if (state.players) {
    state.players.forEach((p, i) => {
      if (players[i]) {
        players[i].life = Number.isFinite(p.life) ? p.life : starting_life;
        players[i].name = (p.name || "").trim() || `Player ${i + 1}`;
        players[i].commander = (p.commander || "").trim();
        players[i].image = (p.image || "").trim() || getDefaultPlayerBackground(i, gameMode);
        players[i].totalTime = p.totalTime || 0;
        players[i].turnTime = p.turnTime || 0;
        players[i].poison = p.poison || 0;
        players[i].commanderDamage = p.commanderDamage || {};
        players[i].monarch = !!p.monarch;
      }
    });
  }

  // Transient interaction state must never persist across refresh.
  isDamageMode = false;
  isDragging = false;
  dragStartIndex = null;
  damageSourceIndex = null;
  damageTargetIndex = null;
  damageAmount = 0;
  damageSelfMode = null;
  selectedDamageTypes = [];
  nonCombatAutoSelected = false;
  cleanupDamageArrow();
  updateUndoButtonState();

  return true;
}

function cloneStateSnapshot(snapshot) {
  return JSON.parse(JSON.stringify(snapshot));
}

function getCurrentStateSnapshot() {
  syncActivePlayerTimer();

  return {
    hasStartedGame,
    gameMode,
    duelSeries,
    starting_life,
    selectedPlayerCount,
    activePlayerIndex,
    isPaused,
    isGameOver,
    winnerIndex,
    turnNumber,
    gameLog,
    lastEliminationCause,
    lastEliminationSelections,
    endGameSelectedCauses,
    matchStats,
    matchEliminations,
    players: players.map(p => ({
      life: p.life,
      name: p.name || "",
      commander: p.commander || "",
      commanderArtId: p.commanderArtId || "",
      image: p.image || "",
      totalTime: p.totalTime || 0,
      turnTime: p.turnTime || 0,
      poison: p.poison || 0,
      commanderDamage: p.commanderDamage || {},
      monarch: !!p.monarch
    }))
  };
}

function applyStateSnapshot(snapshot, { forcePaused = false } = {}) {
  if (!snapshot) return;

  hasStartedGame = !!snapshot.hasStartedGame;
  selectedPlayerCount = Math.min(6, Math.max(2, snapshot.selectedPlayerCount || 4));
  gameMode = snapshot.gameMode === "magic" ? "magic" : "commander";
  duelSeries = normalizeDuelSeriesState(snapshot.duelSeries);
  starting_life = Number.isFinite(snapshot.starting_life) ? snapshot.starting_life : starting_life;
  activePlayerIndex = Math.min(selectedPlayerCount - 1, Math.max(0, snapshot.activePlayerIndex || 0));
  isPaused = !!snapshot.isPaused;
  isGameOver = !!snapshot.isGameOver;
  winnerIndex = snapshot.winnerIndex ?? null;
  turnNumber = Number.isFinite(snapshot.turnNumber) && snapshot.turnNumber > 0 ? snapshot.turnNumber : 1;
  gameLog = Array.isArray(snapshot.gameLog) ? snapshot.gameLog : [];
  lastEliminationCause = snapshot.lastEliminationCause || null;
  lastEliminationSelections = Array.isArray(snapshot.lastEliminationSelections) ? [...snapshot.lastEliminationSelections] : [];
  endGameSelectedCauses = Array.isArray(snapshot.endGameSelectedCauses) ? [...snapshot.endGameSelectedCauses] : [];
  matchStats = Array.isArray(snapshot.matchStats)
    ? Array.from({ length: 6 }, (_, i) => normalizeMatchStat(snapshot.matchStats[i]))
    : createDefaultMatchStats();
  undoStack = Array.isArray(snapshot.undoStack) ? snapshot.undoStack : [];
  matchEliminations = Array.isArray(snapshot.matchEliminations)
    ? Array.from({ length: 6 }, (_, i) => ({
      turn: Number.isFinite(snapshot.matchEliminations[i]?.turn) ? snapshot.matchEliminations[i].turn : null,
      cause: snapshot.matchEliminations[i]?.cause || ""
    }))
    : Array.from({ length: 6 }, () => ({ turn: null, cause: "" }));

  players.forEach((p, i) => {
    const sp = snapshot.players?.[i];
    if (!sp) return;
    p.life = Number.isFinite(sp.life) ? sp.life : starting_life;
    p.name = (sp.name || "").trim() || `Player ${i + 1}`;
    p.commander = (sp.commander || "").trim();
    p.commanderArtId = normalizeCommanderArtId(sp.commanderArtId);
    p.image = (sp.image || "").trim() || getDefaultPlayerBackground(i, gameMode);
    p.totalTime = sp.totalTime || 0;
    p.turnTime = sp.turnTime || 0;
    p.poison = sp.poison || 0;
    p.commanderDamage = sp.commanderDamage || {};
    p.monarch = !!sp.monarch;
  });

  if (forcePaused && !isGameOver) {
    isPaused = true;
  }

  isDamageMode = false;
  isDragging = false;
  dragStartIndex = null;
  damageSourceIndex = null;
  damageTargetIndex = null;
  damageAmount = 0;
  damageSelfMode = null;
  selectedDamageTypes = [];
  nonCombatAutoSelected = false;
  cleanupDamageArrow();

  if (turnInterval) clearInterval(turnInterval);
  turnInterval = null;
  turnStartTime = null;

  render();
  applyLoadedUiState();
  createResetButton();
  updateUndoButtonState();

  if (!isGameOver) {
    startTurnTimer();
  }
}

function pushUndoSnapshot() {
  const snapshot = getCurrentStateSnapshot();
  undoStack.push(cloneStateSnapshot(snapshot));

  if (undoStack.length > MAX_UNDO_STATES) {
    undoStack.shift();
  }

  updateUndoButtonState();
}

function updateUndoButtonState() {
  const undoBtn = document.getElementById("undo-btn");
  const endUndoBtn = document.getElementById("end-undo-btn");
  const isDisabled = undoStack.length === 0;

  if (undoBtn) {
    undoBtn.disabled = isDisabled;
  }

  if (endUndoBtn) {
    endUndoBtn.disabled = isDisabled;
  }
}

function undoLastMove() {
  if (undoStack.length === 0) return;

  const snapshot = undoStack.pop();
  applyStateSnapshot(snapshot, { forcePaused: true });
  updateUndoButtonState();
  saveState();
  triggerHaptic("step");
}

function undoLastMoveFromEndScreen() {
  if (undoStack.length === 0) return;

  const endScreen = document.getElementById("end-screen");
  endScreen?.classList.add("hidden");
  endScreen?.classList.remove("no-winner");

  undoLastMove();
}

function initGame(playerCount) {
  hasStartedGame = true;
  selectedPlayerCount = playerCount;
  activePlayerIndex = 0;
  turnNumber = 1;
  gameLog = [];
  lastEliminationCause = null;
  lastEliminationSelections = [];
  endGameSelectedCauses = [];
  resetMatchStats();

  players.forEach(p => {
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  }
  );

  players.forEach(p => {
  p.poison = 0;
  p.commanderDamage = {};
  p.monarch = false;
});

  document.getElementById("start-screen").classList.add("hidden");

  const gameScreen = document.getElementById("game");
  gameScreen.classList.remove("blurred");
  pauseBtn.classList.remove("hidden");

  startTurnTimer();
  saveState();
  render();
}

function renderStartConfigStep(state) {
  const modeOptions = ["commander", "magic"].map(mode => `
    <button class="${state.mode === mode ? "active" : ""}" data-action="set-mode" data-mode="${mode}">${modeLabel(mode)}</button>
  `).join("");

  const playersOptions = [2, 3, 4, 5, 6].map(count => `
    <button class="${state.playerCount === count ? "active" : ""}" data-action="set-player-count" data-player-count="${count}" ${state.mode === "magic" ? "disabled" : ""}>${count}</button>
  `).join("");

  const duelMatchOptions = [1, 3, 5].map(count => `
    <button class="${state.matchLength === count ? "active" : ""}" data-action="set-match-length" data-match-length="${count}">Bo${count}</button>
  `).join("");

  const lifeOptions = [20, 30, 40, 50, 60].map(life => `
    <button class="${state.startingLife === life ? "active" : ""}" data-action="set-life" data-life="${life}">${life}</button>
  `).join("");

  const jumpBackMarkup = resumeSessions.length
    ? `
      <div class="setup-group">
        <h3>Jump Back In</h3>
        <div class="chip-row">
          ${resumeSessions.map(entry => {
            const snapshot = entry.snapshot || {};
            const names = (snapshot.players || [])
              .slice(0, snapshot.selectedPlayerCount || 0)
              .map((player, index) => getPlayerNameForLog(player, index))
              .join(" | ");
            const when = formatHistoryDateTime(entry.savedAt);
            return `<button data-action="resume-saved-game" data-resume-id="${entry.id}">${escapeHtml(names)} - ${escapeHtml(when)}</button>`;
          }).join("")}
        </div>
      </div>
    `
    : "";

  return `
    <div class="setup-panel setup-panel-start">
      <img class="setup-start-logo" src="./icons/favicon.png" alt="Life Tracker logo">
      <button class="setup-qr-btn setup-icon-circle-btn" data-action="open-qr" aria-label="QR">${getIconMarkup("QR", "setup-inline-icon")}</button>
      <!-- Reset Button -->
      <button class="setup-debug-cache-btn" data-action="debug-clear-cache" aria-label="Clear app cache">Clear Cache</button>
      <!-- -------------------------------------------------------------------------------------------------------------------------- -->
      <div class="setup-group" style="margin-top: 20%;">
        <h3>Select Mode</h3>
        <div class="chip-row">${modeOptions}</div>
      </div>
      <div class="setup-group">
        <h3>${state.mode === "magic" ? "Matches" : "Amount of Players"}</h3>
        <div class="chip-row">${state.mode === "magic" ? duelMatchOptions : playersOptions}</div>
      </div>
      <div class="setup-group">
        <h3>Starting Life</h3>
        <div class="chip-row">${lifeOptions}</div>
      </div>
      <div class="setup-footer" style="margin-top: 5%;">
        <button data-action="continue-from-config">Continue</button>
        <button class="setup-start-logs-btn" data-action="open-start-logs" aria-label="Game Logs">${getIconMarkup("GameLog", "setup-inline-icon")}</button>
      </div>
      ${jumpBackMarkup}
      ${renderQrPanel(state)}
    </div>
  `;
}

function renderQrPanel(state) {
  if (!state?.qrOpen) return "";

  const status = (state.qrStatus || "").trim();
  const isMenu = state.qrView === "menu";
  const shouldShowMenuImportStatus = isMenu && /^Imported\s/i.test(status);
  const statusMarkup = status && (!isMenu || shouldShowMenuImportStatus)
    ? `<div class="qr-status">${escapeHtml(status)}</div>`
    : "";
  const isShare = state.qrView === "share";
  const isScan = state.qrView === "scan";
  const showBackdrop = isShare && !!state.qrImageUrl;
  const menuIntroMarkup = isMenu
    ? `<div class="qr-menu-intro">Copy or Share Player Profiles and Decks</div>`
    : "";

  return `
    <div class="qr-overlay ${showBackdrop ? "qr-overlay-active" : ""}">
      <div class="qr-modal">
        ${isMenu ? `<button class="setup-icon-circle-btn qr-close-btn" data-action="close-qr" aria-label="Close">${getIconMarkup("Cancel", "setup-inline-icon")}</button>` : ""}
        <h3>Transfer Data</h3>
        ${menuIntroMarkup}
        ${statusMarkup}
        ${isMenu ? `
          <div class="setup-footer qr-menu-actions">
            <button data-action="open-qr-scan">Scan</button>
            <button data-action="open-qr-share">Share</button>
          </div>
        ` : ""}
        ${isShare ? `
          <div class="qr-share-body">
            ${state.qrImageUrl ? `<img class="qr-image" src="${state.qrImageUrl}" alt="Transfer QR">` : `<div class="qr-placeholder">QR too large, use copy/share Code.</div>`}
            <textarea class="qr-payload" readonly>${escapeHtml(state.qrSharePayload || "")}</textarea>
            <div class="setup-footer qr-menu-actions qr-menu-actions-inline">
              <button data-action="copy-qr-payload">Copy</button>
              <button data-action="native-share-qr">Share</button>
              <button class="setup-icon-circle-btn qr-back-btn" data-action="back-qr-menu" aria-label="Back">${getIconMarkup("Back", "setup-inline-icon")}</button>
            </div>
          </div>
        ` : ""}
        ${isScan ? `
          <div class="qr-scan-body">
            <video id="qr-scan-video" class="qr-scan-video" autoplay playsinline muted></video>
            <textarea class="qr-payload" data-qr-input="scan-payload" placeholder="Paste your Code here if camera is unavailable.">${escapeHtml(state.qrInput || "")}</textarea>
            <div class="setup-footer qr-menu-actions qr-menu-actions-inline">
              <button data-action="import-qr-payload">Import</button>
              <button class="setup-icon-circle-btn qr-back-btn" data-action="back-qr-menu" aria-label="Back">${getIconMarkup("Back", "setup-inline-icon")}</button>
            </div>
          </div>
        ` : ""}
      </div>
    </div>
  `;
}

function normalizeCommanderArtRef(value) {
  const raw = `${value || ""}`.trim().replace(/^\/+|\/+$/g, "");
  const match = raw.match(/^([a-z0-9]{2,8})\/([a-z0-9]+)$/i);
  if (!match) return "";
  return `/${match[1].toLowerCase()}/${match[2].toLowerCase()}/`;
}

function getDeckTransferArtRef(deck) {
  return normalizeCommanderArtRef(deck?.artRef) || normalizeCommanderArtRef(deck?.artId);
}

function buildScryfallArtCropUrlFromRef(ref) {
  const normalizedRef = normalizeCommanderArtRef(ref);
  if (!normalizedRef) return "";
  const [setCode, collectorNumber] = normalizedRef.replace(/^\/+|\/+$/g, "").split("/");
  if (!setCode || !collectorNumber) return "";
  return `https://api.scryfall.com/cards/${encodeURIComponent(setCode)}/${encodeURIComponent(collectorNumber)}?format=image&version=art_crop`;
}

function buildQrTransferBundle(includeGames = false) {
  const decksByOwner = new Map();
  deckLibrary.forEach((deck) => {
    if (deck?.mode && deck.mode !== "commander") return;
    const ownerId = `${deck?.ownerProfileId || ""}`.trim();
    if (!ownerId) return;
    if (!decksByOwner.has(ownerId)) {
      decksByOwner.set(ownerId, []);
    }
    decksByOwner.get(ownerId).push({
      name: `${deck?.cardName || deck?.deckName || ""}`.trim(),
      artRef: getDeckTransferArtRef(deck)
    });
  });

  const commanderGames = includeGames
    ? trimMatchHistoryByCommanderCap(matchHistory.filter(entry => (entry?.mode || "commander") === "commander"))
    : [];
  const games = includeGames
    ? commanderGames.map((entry) => ({
      sourceEntryId: `${entry?.sourceEntryId || entry?.id || createLocalId()}`.trim(),
      endedAt: Number.isFinite(entry?.endedAt) ? entry.endedAt : Date.now(),
      mode: entry?.mode === "magic" ? "magic" : "commander",
      playerCount: Number.isFinite(entry?.playerCount) ? entry.playerCount : (entry?.players?.length || 0),
      winnerName: `${entry?.winnerName || ""}`.trim(),
      winCause: `${entry?.winCause || ""}`.trim(),
      playerNames: Array.isArray(entry?.players) ? entry.players.map(player => `${player?.name || ""}`.trim()).filter(Boolean) : [],
      commanderNames: Array.isArray(entry?.players) ? entry.players.map(player => `${player?.commander || ""}`.trim()).filter(Boolean) : [],
      commanderArtIds: Array.isArray(entry?.players) ? entry.players.map(player => normalizeCommanderArtId(player?.artId)) : []
    }))
    : [];

  return {
    profiles: profileLibrary
      .map((profile) => {
        const name = `${profile?.name || ""}`.trim();
        if (!name) return null;
        const decks = (decksByOwner.get(profile.id) || [])
          .filter(deck => deck.name)
          .map(deck => ({
            name: deck.name,
            artRef: deck.artRef
          }));
        return {
          name,
          decks
        };
      })
      .filter(Boolean),
    games
  };
}

function encodeQrTransferPayload(bundle) {
  return `${QR_TRANSFER_PREFIX}${toBase64Utf8(JSON.stringify(bundle))}`;
}

function hasDeckImage(deck) {
  const image = `${deck?.image || ""}`.trim();
  return image.length > 0;
}

function normalizeCommanderArtId(value) {
  const raw = `${value || ""}`.trim();
  return /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i.test(raw)
    ? raw
    : "";
}

async function fetchCommanderArtByPrintId(printId) {
  const normalizedId = normalizeCommanderArtId(printId);
  if (!normalizedId) return "";
  const url = `https://api.scryfall.com/cards/${encodeURIComponent(normalizedId)}`;
  try {
    const response = await fetch(url);
    if (!response.ok) return "";
    const card = await response.json();
    if (!isCommanderEligibleCard(card)) return "";
    return getCardArtCrop(card) || "";
  } catch {
    return "";
  }
}

async function fetchCommanderArtByRef(ref) {
  return buildScryfallArtCropUrlFromRef(ref);
}

async function fetchCommanderArtRefByPrintId(printId) {
  const normalizedId = normalizeCommanderArtId(printId);
  if (!normalizedId) return "";
  const url = `https://api.scryfall.com/cards/${encodeURIComponent(normalizedId)}`;
  try {
    const response = await fetch(url);
    if (!response.ok) return "";
    const card = await response.json();
    const setCode = `${card?.set || ""}`.trim();
    const collector = `${card?.collector_number || ""}`.trim();
    return normalizeCommanderArtRef(`${setCode}/${collector}`);
  } catch {
    return "";
  }
}

async function fetchCommanderArtRefByName(name) {
  const cleanName = `${name || ""}`.trim();
  if (!cleanName) return "";

  const exactUrl = `https://api.scryfall.com/cards/named?exact=${encodeURIComponent(cleanName)}`;
  const fuzzyUrl = `https://api.scryfall.com/cards/named?fuzzy=${encodeURIComponent(cleanName)}`;
  const urls = [exactUrl, fuzzyUrl];

  for (const url of urls) {
    try {
      const response = await fetch(url);
      if (!response.ok) continue;
      const card = await response.json();
      const setCode = `${card?.set || ""}`.trim();
      const collector = `${card?.collector_number || ""}`.trim();
      const ref = normalizeCommanderArtRef(`${setCode}/${collector}`);
      if (ref) return ref;
    } catch {
      // Try the next lookup strategy.
    }
  }

  return "";
}

async function hydrateMissingDeckArtRefs({ limit = 24 } = {}) {
  if (navigator.onLine === false) return 0;
  const candidates = deckLibrary.filter(deck =>
    deck?.mode === "commander"
    && !normalizeCommanderArtRef(deck?.artRef)
    && (
      normalizeCommanderArtId(deck?.artId)
      || `${deck?.cardName || deck?.deckName || ""}`.trim()
    )
  ).slice(0, Math.max(1, limit));

  if (!candidates.length) return 0;

  let updatedCount = 0;
  for (const deck of candidates) {
    const artRef = await fetchCommanderArtRefByPrintId(deck.artId)
      || await fetchCommanderArtRefByName(deck.cardName || deck.deckName);
    if (!artRef) continue;
    deck.artRef = artRef;
    updatedCount += 1;
  }

  if (updatedCount > 0) {
    saveDeckLibrary();
  }
  return updatedCount;
}

async function fetchCommanderArtByName(name) {
  const cleanName = `${name || ""}`.trim();
  if (!cleanName) return "";

  const exactUrl = `https://api.scryfall.com/cards/named?exact=${encodeURIComponent(cleanName)}`;
  const fuzzyUrl = `https://api.scryfall.com/cards/named?fuzzy=${encodeURIComponent(cleanName)}`;
  const urls = [exactUrl, fuzzyUrl];

  for (const url of urls) {
    try {
      const response = await fetch(url);
      if (!response.ok) continue;
      const card = await response.json();
      if (!isCommanderEligibleCard(card)) continue;
      const art = getCardArtCrop(card);
      if (art) return art;
    } catch {
      // Ignore fetch failures and try next fallback.
    }
  }
  return "";
}

async function hydrateMissingDeckImages({ limit = 12 } = {}) {
  if (navigator.onLine === false) return 0;
  const candidates = deckLibrary.filter(deck =>
    deck?.mode === "commander" &&
    !hasDeckImage(deck) &&
    (
      normalizeCommanderArtId(deck?.artId)
      || normalizeCommanderArtRef(deck?.artRef || deck?.artId)
      || `${deck?.cardName || deck?.deckName || ""}`.trim()
    )
  ).slice(0, Math.max(1, limit));

  if (!candidates.length) return 0;

  let updatedCount = 0;
  const warmedUrls = [];

  for (const deck of candidates) {
    const art = await fetchCommanderArtByPrintId(deck.artId)
      || await fetchCommanderArtByRef(deck.artRef || deck.artId)
      || await fetchCommanderArtByName(deck.cardName || deck.deckName);
    if (!art) continue;
    deck.image = art;
    warmedUrls.push(art);
    updatedCount += 1;
  }

  if (updatedCount > 0) {
    saveDeckLibrary();
    void warmCommanderImageCacheUrls(warmedUrls);
  }

  return updatedCount;
}

function buildLocalQrDataUrl(payload, size = 360) {
  const raw = `${payload || ""}`.trim();
  if (!raw || typeof window.qrcode !== "function") return "";
  try {
    // typeNumber=0 lets the library auto-pick the smallest QR version.
    const qr = window.qrcode(0, "M");
    qr.addData(raw);
    qr.make();
    const moduleCount = qr.getModuleCount();
    const preferredCellSize = Math.max(2, Math.floor(size / Math.max(1, moduleCount + 8)));
    return qr.createDataURL(preferredCellSize, 4);
  } catch {
    return "";
  }
}

function updateActiveQrStatus(message) {
  const state = ensureSetupState();
  state.qrStatus = `${message || ""}`.trim();
  const statusEl = document.querySelector(".qr-status");
  if (statusEl) {
    statusEl.textContent = state.qrStatus;
  }
}

function formatQrImportStatus(merged) {
  const profileCount = Number.isFinite(merged?.addedProfiles) ? merged.addedProfiles : 0;
  const deckCount = Number.isFinite(merged?.addedDecks) ? merged.addedDecks : 0;
  const gameCount = Number.isFinite(merged?.addedGames) ? merged.addedGames : 0;
  const segments = [`Imported ${profileCount} profiles`, `${deckCount} decks`];
  if (gameCount > 0) {
    segments.push(`${gameCount} games`);
  }
  return `${segments.join(", ")}.`;
}

function parseQrTransferPayload(rawPayload) {
  const raw = `${rawPayload || ""}`.trim();
  if (!raw) return null;

  if (raw.startsWith(QR_TRANSFER_PREFIX)) {
    try {
      const payload = raw.slice(QR_TRANSFER_PREFIX.length);
      return safeJsonParse(fromBase64Utf8(payload), null);
    } catch {
      return null;
    }
  }

  return safeJsonParse(raw, null);
}

function getHistoryShareKey(entry) {
  const sourceEntryId = `${entry?.sourceEntryId || entry?.id || ""}`.trim();
  const sourceDeviceId = `${entry?.createdByDeviceId || entry?.sourceDeviceId || ""}`.trim();
  if (!sourceEntryId) return "";
  return sourceDeviceId ? `${sourceDeviceId}::${sourceEntryId}` : sourceEntryId;
}

function mergeImportedTransferData(payload) {
  if (!payload || typeof payload !== "object") {
    return { addedProfiles: 0, addedDecks: 0, addedGames: 0 };
  }

  const importedProfiles = Array.isArray(payload.profiles) ? payload.profiles : [];
  const nestedProfileDecks = importedProfiles.flatMap((incomingProfile) => {
    const ownerProfileName = `${incomingProfile?.name || ""}`.trim();
    const profileDecks = Array.isArray(incomingProfile?.decks) ? incomingProfile.decks : [];
    return profileDecks.map((deck) => ({
      ...deck,
      ownerProfileName: `${deck?.ownerProfileName || ownerProfileName}`.trim()
    }));
  });
  const importedDecks = nestedProfileDecks;
  const importedGames = Array.isArray(payload.games) ? payload.games : [];

  let addedProfiles = 0;
  let addedDecks = 0;
  let addedGames = 0;

  const ensureProfileIdByName = (name) => {
    const cleanName = `${name || ""}`.trim();
    if (!cleanName) return "";
    const normalized = normalizeLibraryName(cleanName);
    let profile = profileLibrary.find(item => normalizeLibraryName(item.name) === normalized);
    if (!profile) {
      profile = {
        id: createLocalId(),
        name: cleanName,
        lastUsedAt: 0
      };
      profileLibrary.push(profile);
      addedProfiles += 1;
    }
    return profile.id;
  };

  importedProfiles.forEach((incoming) => {
    const incomingName = `${incoming?.name || ""}`.trim();
    if (!incomingName) return;
    const normalized = normalizeLibraryName(incomingName);
    const existing = profileLibrary.find(profile => normalizeLibraryName(profile.name) === normalized);

    if (existing) return;

    const created = {
      id: createLocalId(),
      name: incomingName,
      lastUsedAt: Number.isFinite(incoming?.lastUsedAt) ? incoming.lastUsedAt : 0
    };
    profileLibrary.push(created);
    addedProfiles += 1;
  });

  importedDecks.forEach((incomingDeck) => {
    const commanderName = `${incomingDeck?.name || ""}`.trim();
    if (!commanderName) return;
    const incomingImage = `${incomingDeck?.image || ""}`.trim();
    const incomingArtId = normalizeCommanderArtId(incomingDeck?.artId);
    const incomingArtRef = normalizeCommanderArtRef(incomingDeck?.artRef || incomingDeck?.artId);
    const resolvedIncomingImage = incomingImage || buildScryfallArtCropUrlFromRef(incomingArtRef);

    // Owner name is authoritative for cross-device merging.
    let ownerProfileId = "";
    const ownerName = `${incomingDeck?.ownerProfileName || ""}`.trim();
    if (ownerName) {
      ownerProfileId = ensureProfileIdByName(ownerName);
    }
    if (!ownerProfileId) return;

    const existingDeck = deckLibrary.find(deck =>
      deck.ownerProfileId === ownerProfileId &&
      normalizeLibraryName(deck.cardName || deck.deckName) === normalizeLibraryName(commanderName)
    );
    if (existingDeck) {
      if (!hasDeckImage(existingDeck) && resolvedIncomingImage) {
        existingDeck.image = resolvedIncomingImage;
      }
      if (!normalizeCommanderArtId(existingDeck.artId) && incomingArtId) {
        existingDeck.artId = incomingArtId;
      }
      if (!normalizeCommanderArtRef(existingDeck.artRef) && incomingArtRef) {
        existingDeck.artRef = incomingArtRef;
      }
      return;
    }

    deckLibrary.push({
      id: createLocalId(),
      mode: "commander",
      ownerProfileId,
      deckName: commanderName,
      cardName: commanderName,
      artId: incomingArtId,
      artRef: incomingArtRef,
      image: resolvedIncomingImage,
      lastUsedAt: Number.isFinite(incomingDeck?.lastUsedAt) ? incomingDeck.lastUsedAt : 0
    });
    addedDecks += 1;
  });

  const existingHistoryKeys = new Set(
    matchHistory
      .map(entry => `${entry?.sourceEntryId || entry?.id || ""}`.trim())
      .filter(Boolean)
  );

  importedGames.forEach((incomingGame) => {
    const sourceEntryId = `${incomingGame?.sourceEntryId || incomingGame?.id || ""}`.trim();
    if (!sourceEntryId || existingHistoryKeys.has(sourceEntryId)) return;

    const playerNames = Array.isArray(incomingGame?.playerNames) ? incomingGame.playerNames : [];
    const commanderNames = Array.isArray(incomingGame?.commanderNames) ? incomingGame.commanderNames : [];
    const commanderArtIds = Array.isArray(incomingGame?.commanderArtIds) ? incomingGame.commanderArtIds : [];
    const playerDeckImages = [];
    const playerDeckArtIds = [];

    playerNames.forEach((playerName, index) => {
      const profileId = ensureProfileIdByName(playerName);
      if (!profileId) {
        playerDeckImages[index] = "";
        playerDeckArtIds[index] = "";
        return;
      }
      const commanderName = `${commanderNames[index] || ""}`.trim();
      const commanderArtId = normalizeCommanderArtId(commanderArtIds[index]);
      if (!commanderName) {
        playerDeckImages[index] = "";
        playerDeckArtIds[index] = "";
        return;
      }

      const existingDeck = deckLibrary.find(deck =>
        deck.ownerProfileId === profileId &&
        normalizeLibraryName(deck.cardName || deck.deckName) === normalizeLibraryName(commanderName)
      );

      if (existingDeck) {
        if (!normalizeCommanderArtId(existingDeck.artId) && commanderArtId) {
          existingDeck.artId = commanderArtId;
        }
        playerDeckImages[index] = `${existingDeck.image || ""}`.trim();
        playerDeckArtIds[index] = normalizeCommanderArtId(existingDeck.artId) || commanderArtId;
        return;
      }

      deckLibrary.push({
        id: createLocalId(),
        mode: "commander",
        ownerProfileId: profileId,
        deckName: commanderName,
        cardName: commanderName,
        artId: commanderArtId,
        artRef: "",
        image: "",
        lastUsedAt: 0
      });
      playerDeckImages[index] = "";
      playerDeckArtIds[index] = commanderArtId;
      addedDecks += 1;
    });

    const playersSummary = playerNames.map((name, index) => ({
      name: `${name || ""}`.trim() || `Player ${index + 1}`,
      commander: `${commanderNames[index] || ""}`.trim(),
      artId: normalizeCommanderArtId(playerDeckArtIds[index]),
      image: playerDeckImages[index] || getDefaultPlayerBackground(index, "commander"),
      totalTime: 0,
      finalLife: 0,
      finalPoison: 0,
      stats: createDefaultMatchStat(),
      eliminationTurn: null,
      eliminationCause: "",
      isWinner: false
    }));

    matchHistory.push(normalizeMatchHistoryEntry({
      id: createLocalId(),
      sourceEntryId,
      createdByDeviceId: "",
      endedAt: Number.isFinite(incomingGame?.endedAt) ? incomingGame.endedAt : Date.now(),
      mode: incomingGame?.mode === "magic" ? "magic" : "commander",
      playerCount: Number.isFinite(incomingGame?.playerCount) ? incomingGame.playerCount : playersSummary.length,
      winnerIndex: -1,
      winnerName: `${incomingGame?.winnerName || ""}`.trim(),
      winCause: `${incomingGame?.winCause || ""}`.trim(),
      finalMessage: `${incomingGame?.winCause || ""}`.trim(),
      totalMatchSeconds: 0,
      turnCount: 0,
      actionCount: 0,
      players: playersSummary,
      gameLog: []
    }));
    existingHistoryKeys.add(sourceEntryId);
    addedGames += 1;
  });

  profileLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
  deckLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
  matchHistory.sort((a, b) => (b.endedAt || 0) - (a.endedAt || 0));
  matchHistory = trimMatchHistoryByCommanderCap(matchHistory);

  saveProfileLibrary();
  saveDeckLibrary();
  saveMatchHistory();
  void warmCommanderImageCache();
  void hydrateMissingDeckImages();

  return { addedProfiles, addedDecks, addedGames };
}

function stopQrScanner() {
  if (qrScannerLoopId !== null) {
    window.cancelAnimationFrame(qrScannerLoopId);
    qrScannerLoopId = null;
  }
  if (qrScannerStream) {
    qrScannerStream.getTracks().forEach(track => track.stop());
    qrScannerStream = null;
  }
  qrScannerDetector = null;
}

async function startQrScanner() {
  stopQrScanner();
  const state = ensureSetupState();
  if (!state.qrOpen || state.qrView !== "scan") return;

  const videoEl = document.getElementById("qr-scan-video");
  if (!videoEl) return;

  try {
    if (!navigator.mediaDevices || typeof navigator.mediaDevices.getUserMedia !== "function") {
      throw new Error("media-unavailable");
    }
    const constraints = [
      { video: { facingMode: { ideal: "environment" } }, audio: false },
      { video: true, audio: false }
    ];
    let lastError = null;
    for (const constraint of constraints) {
      try {
        qrScannerStream = await navigator.mediaDevices.getUserMedia(constraint);
        break;
      } catch (error) {
        lastError = error;
      }
    }
    if (!qrScannerStream) {
      throw lastError || new Error("camera-unavailable");
    }
  } catch {
    state.qrStatus = "Unable to access camera. Paste payload below.";
    renderStartSetupScreen();
    return;
  }

  videoEl.setAttribute("autoplay", "");
  videoEl.setAttribute("muted", "");
  videoEl.setAttribute("playsinline", "");
  videoEl.autoplay = true;
  videoEl.muted = true;
  videoEl.playsInline = true;
  videoEl.srcObject = qrScannerStream;
  await videoEl.play().catch(() => {});

  if (!("BarcodeDetector" in window)) {
    updateActiveQrStatus("Camera preview is on, but live QR decoding is unavailable here. Paste Code below.");
    return;
  }

  try {
    qrScannerDetector = new window.BarcodeDetector({ formats: ["qr_code"] });
  } catch {
    updateActiveQrStatus("Camera preview is on, but QR decoding is unavailable here. Paste payload below.");
    return;
  }

  const loop = async () => {
    const current = ensureSetupState();
    if (!current.qrOpen || current.qrView !== "scan") {
      stopQrScanner();
      return;
    }

    try {
      const results = await qrScannerDetector.detect(videoEl);
      const rawValue = results?.[0]?.rawValue || "";
      if (rawValue) {
        current.qrInput = rawValue;
        const parsed = parseQrTransferPayload(rawValue);
        if (!parsed) {
          current.qrStatus = "QR data is invalid.";
          renderStartSetupScreen();
          stopQrScanner();
          return;
        }

        const merged = mergeImportedTransferData(parsed);
        current.qrView = "menu";
        current.qrStatus = formatQrImportStatus(merged);
        current.qrInput = "";
        renderStartSetupScreen();
        stopQrScanner();
        return;
      }
    } catch {
      // Ignore intermittent decode errors; continue scanning loop.
    }

    qrScannerLoopId = window.requestAnimationFrame(loop);
  };

  qrScannerLoopId = window.requestAnimationFrame(loop);
}

function isCommanderSeatReady(seat) {
  return !!((seat?.profileId || "").trim() && (seat?.deckId || "").trim());
}

function allCommanderSeatsReady(state) {
  return Array.from({ length: state.playerCount }, (_, i) => i).every(i => isCommanderSeatReady(state.seats[i]));
}

function allSetupSeatsReady(state) {
  if (!state) return false;
  if (state.mode === "magic") return true;
  return allCommanderSeatsReady(state);
}

function hasAnySelectedProfile(state) {
  if (!state) return false;
  return state.seats.some(seat => !!((seat?.profileId || "").trim()));
}

function shouldUseBoardStarterSelection(state = setupState) {
  return !!(
    setupGridPreviewActive &&
    state &&
    state.step === "seats" &&
    !state.forceDeckSelection &&
    allSetupSeatsReady(state)
  );
}

function shouldShowSetupActiveSeat() {
  return shouldUseBoardStarterSelection();
}

function buildRematchSetupState() {
  const playerCount = Math.min(6, Math.max(2, selectedPlayerCount || 4));
  const mode = gameMode === "magic" ? "magic" : "commander";
  const previousState = setupState;
  const seats = Array.from({ length: 6 }, (_, index) => {
    const baseSeat = getDefaultSeatState(index);
    const previousSeat = previousState?.seats?.[index];
    const currentPlayer = players[index];
    const profileName = (previousSeat?.profileName || currentPlayer?.name || baseSeat.profileName || "").trim() || baseSeat.profileName;
    const seat = {
      ...baseSeat,
      profileId: typeof previousSeat?.profileId === "string" ? previousSeat.profileId : "",
      profileName
    };
    if (mode === "magic") {
      seat.image = getDefaultPlayerBackground(index, mode);
    }
    return seat;
  });

  return {
    step: "seats",
    mode,
    playerCount: mode === "magic" ? 2 : playerCount,
    matchLength: duelSeries.matchLength,
    startingLife: starting_life,
    startingPlayerIndex: 0,
    showStarterPicker: false,
    forceDeckSelection: mode === "commander",
    seats
  };
}

function renderCommanderGridSeat(state, playerIndex, seatPos) {
  const seat = state.seats[playerIndex];
  const profileOptions = [`<option value="">Select profile</option>`]
    .concat(profileLibrary.map(profile => {
      const isUsedElsewhere = isProfileSelectedInOtherSeat(state, profile.id, playerIndex);
      return `<option value="${profile.id}" ${seat.profileId === profile.id ? "selected" : ""} ${isUsedElsewhere ? "disabled" : ""}>${profile.name}</option>`;
    }))
    .join("");

  const deckOptions = [`<option value="">Select deck</option>`]
    .concat(deckLibrary
      .filter(deck => deck.mode !== "magic")
      .map(deck => `<option value="${deck.id}" ${seat.deckId === deck.id ? "selected" : ""}>${deck.deckName || deck.cardName}</option>`))
    .join("");

  const hasProfile = !!(seat.profileId && (seat.profileName || "").trim());
  const hasDeck = !!((seat.cardName || "").trim() && (seat.image || "").trim());
  const artStyle = hasDeck ? `style="background-image:url('${seat.image.replace(/'/g, "\\'")}')"` : "";

  let content = "";
  if (!hasProfile) {
    content = `
      <div class="setup-seat-step">
        <div class="setup-seat-title">Select Profile</div>
        <div class="setup-inline">
          <select data-seat-profile-select="${playerIndex}">${profileOptions}</select>
          <button data-action="apply-profile" data-seat="${playerIndex}">Use</button>
        </div>
        <button class="setup-plus-btn" data-action="add-profile" data-seat="${playerIndex}">+</button>
      </div>
    `;
  } else if (!hasDeck) {
    content = `
      <div class="setup-seat-step setup-seat-step-with-nav">
        <button class="setup-seat-back-btn" data-action="go-back-profile-seat" data-seat="${playerIndex}" aria-label="Back to player selection">
          <span class="icon-mask setup-back-icon" style="--icon:url('./icons/Back.svg')"></span>
        </button>
        <div class="setup-seat-title setup-seat-title-selected">${seat.profileName}</div>
        <div class="setup-inline">
          <select data-seat-deck-select="${playerIndex}">${deckOptions}</select>
          <button data-action="apply-deck" data-seat="${playerIndex}">Use</button>
        </div>
        <button class="setup-plus-btn" data-action="add-deck" data-seat="${playerIndex}">+</button>
        <input type="text" data-seat-input="deckName" data-seat="${playerIndex}" value="${seat.deckName || ""}" placeholder="Deck name">
        <input type="text" data-seat-deck-search="${playerIndex}" placeholder="Search commander">
        <div class="setup-search-results" id="search-results-${playerIndex}"></div>
      </div>
    `;
  } else {
    content = `
      <div class="setup-seat-step setup-seat-step-with-nav setup-seat-ready">
        <button class="setup-seat-back-btn" data-action="go-back-profile-seat" data-seat="${playerIndex}" aria-label="Back to player selection">
          <span class="icon-mask setup-back-icon" style="--icon:url('./icons/Back.svg')"></span>
        </button>
        <div class="setup-seat-title setup-seat-title-selected">${seat.profileName}</div>
        <div class="setup-art-preview" ${artStyle}></div>
        <div class="setup-meta">${getSeatDeckLabel(seat)}</div>
        <button data-action="reset-seat" data-seat="${playerIndex}">Change</button>
      </div>
    `;
  }

  return `
    <div class="setup-grid-seat setup-grid-seat-${seatPos}" data-seat="${playerIndex}">
      ${content}
    </div>
  `;
}

function renderCommanderSeatOverlay(state, playerIndex) {
  const seat = state.seats[playerIndex];
  const profileDecks = getDecksForProfile(seat.profileId);
  const borrowProfiles = profileLibrary.filter(profile => profile.id !== seat.profileId);
  const borrowProfileName = borrowProfiles.find(profile => profile.id === seat.borrowProfileId)?.name || "";
  const borrowDecks = getDecksForProfile(seat.borrowProfileId);
  const visibleDecks = seat.isBorrowingDeck ? borrowDecks : profileDecks;

  const hasProfile = !!(seat.profileId && (seat.profileName || "").trim());
  const hasDeck = !!(seat.deckId && (seat.cardName || "").trim() && (seat.image || "").trim());
  const artStyle = hasDeck ? `style="background-image:url('${seat.image.replace(/'/g, "\\'")}')"` : "";
  const selectedDeckName = getSeatDeckLabel(seat);
  const backButton = `
    <button class="setup-seat-back-btn" data-action="go-back-profile-seat" data-seat="${playerIndex}" aria-label="Back to player selection">
      ${getIconMarkup("Back", "setup-back-icon")}
    </button>
  `;

  if (!hasProfile) {
    const profileAction = seat.isDeletingProfile ? "delete-profile" : "select-profile";
    const canDeleteProfiles = profileLibrary.length > 0;
    const profileButtons = profileLibrary.length
      ? `
        <div class="setup-profile-list">
          ${profileLibrary.map(profile => `
            <button class="setup-profile-btn ${seat.profileId === profile.id ? "active" : ""} ${seat.isDeletingProfile ? "is-delete-mode" : ""}" data-action="${profileAction}" data-seat="${playerIndex}" data-profile-id="${profile.id}" ${!seat.isDeletingProfile && isProfileSelectedInOtherSeat(state, profile.id, playerIndex) ? "disabled" : ""}>
              ${profile.name}
            </button>
          `).join("")}
        </div>
      `
      : `<div class="setup-meta">No profiles yet.</div>`;

    const addProfilePanel = seat.isAddingProfile
      ? `
        <div class="setup-add-profile-panel">
          <div class="setup-seat-title">New Player</div>
          <input type="text" class="${seat.hasDuplicateProfileName ? "setup-input-invalid" : ""}" data-seat-input="newProfileName" data-seat="${playerIndex}" value="${seat.newProfileName || ""}" placeholder="Player name">
          <button data-action="create-profile" data-seat="${playerIndex}" ${seat.hasDuplicateProfileName ? "disabled" : ""}>Create</button>
        </div>
      `
      : "";

    return `
      <div class="setup-seat-overlay ${seat.isAddingProfile ? "setup-seat-overlay-searching" : ""}">
        ${seat.isAddingProfile ? `
          ${backButton.replace("go-back-profile-seat", "close-add-profile").replace("Back to player selection", "Back from profile creation")}
          <div class="setup-seat-header">
            <div class="setup-seat-title">Select Profile</div>
          </div>
          ${addProfilePanel}
        ` : `
          <div class="setup-seat-title">${seat.isDeletingProfile ? "DELETE PLAYER" : "Select Profile"}</div>
          ${profileButtons}
          ${seat.isDeletingProfile ? "" : `<button class="setup-plus-btn" data-action="add-profile" data-seat="${playerIndex}">+</button>`}
          ${canDeleteProfiles ? `<button class="setup-minus-btn ${seat.isDeletingProfile ? "active" : ""}" data-action="${seat.isDeletingProfile ? "close-delete-profile" : "open-delete-profile"}" data-seat="${playerIndex}" aria-label="Delete player mode">-</button>` : ""}
        `}
      </div>
    `;
  }

  const deckAction = seat.isDeletingDeck ? "delete-deck" : "select-deck";
  const canDeleteDecks = profileDecks.length > 0;
  const deckGrid = visibleDecks.length
    ? `
      <div class="setup-deck-grid ${seat.isBorrowingDeck ? "setup-deck-grid-full" : ""}">
        ${visibleDecks.map(deck => {
          const isUnavailable = !seat.isDeletingDeck && isDeckSelectedInOtherSeat(state, deck.id, playerIndex);
          return `
          <button class="setup-deck-thumb ${seat.deckId === deck.id ? "active" : ""} ${seat.isDeletingDeck ? "is-delete-mode" : ""} ${isUnavailable ? "is-unavailable" : ""}" data-action="${deckAction}" data-seat="${playerIndex}" data-deck-id="${deck.id}" ${isUnavailable ? "disabled" : ""}>
            <img src="${deck.image}" alt="${deck.cardName}">
          </button>
        `;
        }).join("")}
      </div>
    `
    : `<div class="setup-meta setup-empty-state ${seat.isBorrowingDeck ? "setup-empty-state-full" : ""}">${seat.isBorrowingDeck ? (seat.borrowProfileId ? `No decks yet for ${borrowProfileName}.` : "Select a player to borrow a deck from.") : `No decks yet for ${seat.profileName}.`}</div>`;

  const addPanel = seat.isAddingDeck
    ? `
      <div class="setup-add-deck-panel">
        ${seat.pendingSearchCard
          ? `
            <div class="setup-art-choice-header">
              <div class="setup-meta">Choose art for ${escapeHtml(seat.pendingSearchCard.name || "")}</div>
            </div>
            ${seat.isLoadingArtOptions
              ? `<div class="setup-meta">Loading print arts...</div>`
              : `
                ${(seat.searchArtOptions || []).length
                  ? `
                    <div class="setup-search-art-grid">
                      ${(seat.searchArtOptions || []).map((option) => `
                        <button class="setup-search-art-thumb" data-action="select-search-art" data-seat="${playerIndex}" data-art-id="${escapeHtml(option.id)}">
                          <img src="${option.art}" alt="${escapeHtml(seat.pendingSearchCard.name || "Commander art")}">
                          <span>${escapeHtml(option.setLabel || "Print")}</span>
                        </button>
                      `).join("")}
                    </div>
                  `
                  : `<div class="setup-meta">No print arts found. Try another search.</div>`
                }
              `
            }
          `
          : `
            <input type="text" data-seat-deck-search="${playerIndex}" placeholder="Search commander">
            <div class="setup-search-results" id="search-results-${playerIndex}"></div>
          `
        }
      </div>
    `
    : "";

  const borrowPanel = seat.isBorrowingDeck
    ? `
      <div class="setup-seat-body">
        ${seat.borrowProfileId ? `
          ${deckGrid}
        ` : `
          <div class="setup-profile-list setup-profile-list-full">
            ${borrowProfiles.map(profile => `
              <button class="setup-profile-btn" data-action="select-borrow-profile" data-seat="${playerIndex}" data-profile-id="${profile.id}">
                ${profile.name}
              </button>
            `).join("")}
          </div>
          ${borrowProfiles.length ? "" : `<div class="setup-meta">No other players to borrow from yet.</div>`}
        `}
      </div>
    `
    : "";

  const deckBackButton = seat.isBorrowingDeck
    ? `
      <button class="setup-seat-back-btn" data-action="${seat.borrowProfileId ? "back-borrow-profile" : "close-borrow-deck"}" data-seat="${playerIndex}" aria-label="Back from borrow deck">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
    `
    : seat.isAddingDeck
    ? `
      <button class="setup-seat-back-btn" data-action="close-add-deck" data-seat="${playerIndex}" aria-label="Back from commander search">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
    `
    : backButton;

  return `
    <div class="setup-seat-overlay ${hasDeck ? "setup-seat-ready" : ""} ${seat.isAddingDeck ? "setup-seat-overlay-searching" : ""}">
      ${seat.isDeletingDeck ? "" : deckBackButton}
      <div class="setup-seat-header">
        <div class="setup-seat-title ${(!seat.isDeletingDeck && !seat.isBorrowingDeck) ? "setup-seat-title-selected" : ""}">${seat.isDeletingDeck ? "DELETE DECK" : seat.isBorrowingDeck ? `Borrow Deck${seat.borrowProfileId ? ` from ${borrowProfileName}` : ""}` : seat.profileName}</div>
        ${(seat.isAddingDeck || seat.isDeletingDeck || seat.isBorrowingDeck) ? "" : (selectedDeckName ? `<div class="setup-meta setup-seat-subtitle">${selectedDeckName}</div>` : "")}
      </div>
      ${seat.isAddingDeck ? addPanel : seat.isBorrowingDeck ? borrowPanel : `
        <div class="setup-seat-body">
          ${deckGrid}
        </div>
        ${seat.isDeletingDeck ? "" : `<button class="setup-plus-btn" data-action="add-deck" data-seat="${playerIndex}">+</button>`}
        ${canDeleteDecks ? `<button class="setup-minus-btn ${seat.isDeletingDeck ? "active" : ""}" data-action="${seat.isDeletingDeck ? "close-delete-deck" : "open-delete-deck"}" data-seat="${playerIndex}" aria-label="Delete deck mode">-</button>` : ""}
        ${seat.isDeletingDeck ? "" : `<button class="setup-borrow-btn" data-action="open-borrow-deck" data-seat="${playerIndex}" aria-label="Borrow deck">Borrow</button>`}
      `}
    </div>
  `;
}

function exitSetupGridPreview() {
  if (!setupGridPreviewActive) return;
  setupGridPreviewActive = false;
  document.body.classList.remove("setup-grid-mode");
  document.body.dataset.players = "0";
  if (selectedPlayerCount === 0) {
    game.innerHTML = '<svg id="damage-arrow-layer"></svg>';
    game.dataset.players = "0";
  } else {
    render();
  }
}

function renderCommanderGridOnGame(state) {
  setupGridPreviewActive = true;
  document.body.classList.add("setup-grid-mode");
  pauseBtn.classList.add("hidden");
  setPauseButtonIcon(false);
  state.showStarterPicker = false;

  selectedPlayerCount = state.playerCount;
  activePlayerIndex = Math.min(state.playerCount - 1, Math.max(0, state.startingPlayerIndex || 0));
  isPaused = true;

  players.forEach((p, index) => {
    const seat = state.seats[index] || getDefaultSeatState(index);
    p.life = state.startingLife;
    p.name = (seat.profileName || "").trim() || `Player ${index + 1}`;
    p.commander = state.mode === "magic" ? "" : ((seat.cardName || "").trim());
    p.commanderArtId = state.mode === "magic" ? "" : normalizeCommanderArtId(seat.artId);
    p.image = getSeatBackgroundImage(seat, index, state.mode);
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  });

  render();

  const activeIndices = [...Array(state.playerCount).keys()];
  const useBoardStarterSelection = shouldUseBoardStarterSelection(state);
  activeIndices.forEach((playerIndex) => {
    const playerEl = document.getElementById(`player${playerIndex}`);
    const info = playerEl?.querySelector(".info_container");
    if (!playerEl || !info) return;
    playerEl.classList.add("setup-seat-player");
    if (!useBoardStarterSelection) {
      info.innerHTML = renderCommanderSeatOverlay(state, playerIndex);
      bindSetupSeatBodyDrag(playerEl, playerIndex);
      updateScrollableFadeState(info);
    }
  });

  const existingCenterPlay = document.getElementById("setup-center-play");
  if (existingCenterPlay) existingCenterPlay.remove();
  const existingCenterBack = document.getElementById("setup-center-back");
  if (existingCenterBack) existingCenterBack.remove();
  const existingStarterPicker = document.getElementById("setup-starter-picker-anchor");
  if (existingStarterPicker) existingStarterPicker.remove();

  const showingStarterSelection = shouldUseBoardStarterSelection(state);
  if (allSetupSeatsReady(state) && showingStarterSelection) {
    const playBtn = document.createElement("button");
    playBtn.id = "setup-center-play";
    playBtn.className = "setup-center-play";
    playBtn.dataset.action = "start-configured-game";
    playBtn.setAttribute("aria-label", "Start game");
    playBtn.innerHTML = getIconMarkup("Play", "btn-icon");
    game.appendChild(playBtn);
    if (state.mode === "commander") {
      const backBtn = document.createElement("button");
      backBtn.id = "setup-center-back";
      backBtn.className = "setup-center-back setup-center-back-side";
      backBtn.dataset.action = "back-from-board-starter";
      backBtn.setAttribute("aria-label", "Back to commander selection");
      backBtn.innerHTML = getIconMarkup("Back", "btn-icon");
      game.appendChild(backBtn);
    }
  } else if (!hasAnySelectedProfile(state)) {
    const backBtn = document.createElement("button");
    backBtn.id = "setup-center-back";
    backBtn.className = "setup-center-back";
    backBtn.dataset.action = "back-to-config";
    backBtn.setAttribute("aria-label", "Back");
    backBtn.innerHTML = getIconMarkup("Back", "btn-icon");
    game.appendChild(backBtn);
  }

  updateCommanderOverlayAnchors();
  updateScrollableFadeState(document);
}

function syncSetupSeatPreviewPlayer(state, seatIndex) {
  const seat = state?.seats?.[seatIndex] || getDefaultSeatState(seatIndex);
  const player = players[seatIndex];
  if (!player) return;
  player.life = state?.startingLife || player.life;
  player.name = (seat.profileName || "").trim() || `Player ${seatIndex + 1}`;
  player.commander = state?.mode === "magic" ? "" : ((seat.cardName || "").trim());
  player.commanderArtId = state?.mode === "magic" ? "" : normalizeCommanderArtId(seat?.artId);
  player.image = getSeatBackgroundImage(seat, seatIndex, state?.mode);
}

function refreshSetupSeatOverlay(seatIndex) {
  if (!setupGridPreviewActive) return false;
  const state = ensureSetupState();
  if (shouldUseBoardStarterSelection(state) || (allSetupSeatsReady(state) && !state.forceDeckSelection)) {
    renderStartSetupScreen();
    return true;
  }

  syncSetupSeatPreviewPlayer(state, seatIndex);
  const playerEl = document.getElementById(`player${seatIndex}`);
  const info = playerEl?.querySelector(".info_container");
  const bg = playerEl?.querySelector(".bg");
  if (!playerEl || !info || !bg) return false;

  playerEl.classList.add("setup-seat-player");
  info.innerHTML = renderCommanderSeatOverlay(state, seatIndex);
  bg.style.backgroundImage = players[seatIndex].image ? `url(${players[seatIndex].image})` : "none";
  bindSetupSeatBodyDrag(playerEl, seatIndex);
  updateScrollableFadeState(info);
  updateCommanderOverlayAnchors();
  return true;
}

function updateScrollableFadeState(root = document) {
  const apply = () => {
    root.querySelectorAll(".setup-profile-list").forEach((list) => {
      const isScrollable = (list.scrollHeight - list.clientHeight) > 2;
      list.classList.toggle("is-scrollable", isScrollable);
    });
  };

  apply();
  window.requestAnimationFrame(apply);
}

function bindSetupSeatBodyDrag(playerEl, seatIndex) {
  const scrollers = playerEl
    ? Array.from(playerEl.querySelectorAll(".setup-seat-body, .setup-search-results, .setup-profile-list, .setup-deck-grid, .setup-search-art-grid"))
    : [];
  if (!scrollers.length) return;

  const seatRotation = getSeatRotation(selectedPlayerCount, seatIndex);
  const usesSidewaysDrag = Math.abs(seatRotation) === 90;
  scrollers.forEach((scroller) => {
    bindDragScroll(scroller, { usesSidewaysDrag, seatRotation, ignoreSelectors: "input, select" });
  });
}

function bindDragScroll(scroller, { usesSidewaysDrag = false, seatRotation = 0, ignoreSelectors = "" } = {}) {
  if (!scroller || scroller.dataset.dragBound === "1") return;
  let startX = 0;
  let startY = 0;
  let startScrollTop = 0;
  let pointerId = null;
  let dragging = false;

  scroller.dataset.dragBound = "1";
  scroller.dataset.scrollAxis = usesSidewaysDrag ? "sideways-drag" : "vertical-drag";

  scroller.addEventListener("pointerdown", (event) => {
    if (ignoreSelectors && event.target.closest(ignoreSelectors)) return;
    pointerId = event.pointerId;
    startX = event.clientX;
    startY = event.clientY;
    startScrollTop = scroller.scrollTop;
    dragging = false;
    scroller.setPointerCapture(event.pointerId);
  });

  scroller.addEventListener("pointermove", (event) => {
    if (pointerId !== event.pointerId) return;
    const deltaX = event.clientX - startX;
    const deltaY = event.clientY - startY;

    if (!dragging && Math.abs(deltaX) + Math.abs(deltaY) > 6) {
      dragging = true;
      scroller.dataset.dragging = "1";
    }
    if (!dragging) return;

    if (usesSidewaysDrag) {
      // Side-drag mode for rotated seats: horizontal finger movement drives list scroll.
      // Keep direction consistent across both +90 and -90 seats.
      scroller.scrollTop = startScrollTop + deltaX;
    } else {
      scroller.scrollTop = startScrollTop - deltaY;
    }
    event.preventDefault();
  });

  const clearPointer = (event) => {
    if (pointerId !== event.pointerId) return;
    if (dragging) {
      window.setTimeout(() => {
        delete scroller.dataset.dragging;
      }, 80);
    } else {
      delete scroller.dataset.dragging;
    }
    dragging = false;
    pointerId = null;
  };

  scroller.addEventListener("pointerup", clearPointer);
  scroller.addEventListener("pointercancel", clearPointer);
  scroller.addEventListener("click", (event) => {
    if (scroller.dataset.dragging === "1") {
      event.preventDefault();
      event.stopPropagation();
    }
  }, true);
}

function renderCommanderGridStep(state) {
  const order = getPlayerOrder(state.playerCount);
  const seatCards = order
    .map((playerIndex, seatPos) => renderCommanderGridSeat(state, playerIndex, seatPos))
    .join("");
  const ready = allSetupSeatsReady(state);
  const playButton = ready
    ? `<button class="setup-center-play" data-action="start-configured-game" aria-label="Start game">${getIconMarkup("Play", "btn-icon")}</button>`
    : "";

  return `
    <div class="setup-panel setup-panel-wide">
      <h2>Player Setup</h2>
      <div class="setup-board setup-board-${state.playerCount}">
        ${seatCards}
        ${playButton}
      </div>
      <div class="setup-footer">
        <button data-action="back-to-config">Back</button>
      </div>
    </div>
  `;
}

function renderStartingPlayerStep(state, options = {}) {
  const { modal = false, backAction = "back-from-starter" } = options;
  const isDuelSeriesSetup = state.mode === "magic" && normalizeDuelMatchLength(state.matchLength) > 1;
  const duelGameNumber = Number(pendingDuelContinuation?.nextSeries?.currentGame) || 1;
  const title = isDuelSeriesSetup
    ? `Starting Player Game ${duelGameNumber}`
    : "Choose Starting Player";
  const seatButtons = Array.from({ length: state.playerCount }, (_, seatIndex) => {
    const seat = state.seats[seatIndex];
    const name = (seat.profileName || "").trim() || `Player ${seatIndex + 1}`;
    return `<button class="${state.startingPlayerIndex === seatIndex ? "active" : ""}" data-action="set-starting-player" data-seat="${seatIndex}">${name}</button>`;
  }).join("");
  const wrapperClass = modal ? "setup-starter-modal" : "setup-panel";
  return `
    <div class="${wrapperClass}">
      <h2>${title}</h2>
      <div class="chip-row">${seatButtons}</div>
      <div class="setup-footer">
        <button data-action="${backAction}">Back</button>
        <button data-action="start-configured-game">Start Game</button>
      </div>
    </div>
  `;
}

function renderStartSetupScreen() {
  const container = document.getElementById("player-buttons");
  const startScreen = document.getElementById("start-screen");
  if (!container || !startScreen) return;
  const state = ensureSetupState();
  renderStartScreenBackdrop();
  startScreen.classList.remove("hidden");
  container.classList.remove("hidden");
  startScreen.classList.add("setup-open");

  if (state.step === "config") {
    exitSetupGridPreview();
    container.innerHTML = renderStartConfigStep(state);
  } else if (state.step === "history") {
    stopQrScanner();
    state.qrOpen = false;
    exitSetupGridPreview();
    container.innerHTML = renderStartHistoryScreen();
  } else if (state.step === "seats") {
    stopQrScanner();
    state.qrOpen = false;
    renderCommanderGridOnGame(state);
    container.innerHTML = "";
  } else {
    stopQrScanner();
    state.qrOpen = false;
    exitSetupGridPreview();
    container.innerHTML = pendingDuelContinuation
      ? renderStartingPlayerStep(state, { backAction: "back-from-duel-next-starter" })
      : renderStartingPlayerStep(state);
  }

  updateScrollableFadeState(container);
}

function renderDuelSeriesOverlay(playerIndex) {
  if (!isDuelMode() || selectedPlayerCount !== 2) return "";
  const matchLength = normalizeDuelMatchLength(duelSeries.matchLength);
  if (matchLength <= 1) return "";
  const winsNeeded = getDuelWinsNeeded(matchLength);
  const wins = duelSeries.wins?.[playerIndex] || 0;
  const tokenMarkup = Array.from({ length: winsNeeded }, (_, index) => `
    <span class="duel-series-token ${index < wins ? "is-won" : ""}">
      <span class="duel-series-token-shape" aria-hidden="true"></span>
    </span>
  `).join("");
  return `
    <div class="duel-series-overlay" aria-label="Series wins">
      <div class="duel-series-track">${tokenMarkup}</div>
    </div>
  `;
}

async function searchScryfallCards(query, { commanderOnly = false } = {}) {
  const clean = (query || "").trim();
  if (clean.length < 2) return [];
  const q = `${clean} game:paper legal:commander is:commander`;
  const url = `https://api.scryfall.com/cards/search?unique=cards&order=name&dir=asc&q=${encodeURIComponent(q)}`;
  const controller = new AbortController();
  const timeoutId = window.setTimeout(() => controller.abort(), SCRYFALL_SEARCH_TIMEOUT_MS);
  try {
    const response = await fetch(url, { signal: controller.signal });
    if (!response.ok) return [];
    const payload = await response.json();
    const cards = Array.isArray(payload.data) ? payload.data : [];
    return cards
      .filter(card => isCommanderEligibleCard(card))
      .sort((a, b) => scoreCommanderSearchResult(clean, b) - scoreCommanderSearchResult(clean, a))
      .slice(0, 8)
      .map(card => ({
        id: card.id,
        name: card.name || "",
        art: getCardArtCrop(card),
        printsUri: card.prints_search_uri || "",
        typeLine: card.type_line || "",
        exact: `${card.name || ""}`.trim().toLowerCase() === clean.toLowerCase()
      }))
      .filter(card => card.art);
  } catch {
    return [];
  } finally {
    window.clearTimeout(timeoutId);
  }
}

async function fetchCommanderPrintArts(card) {
  if (!card?.name) return [];
  const fallback = card.art
    ? [{
      id: `${card.id || card.name}-base`,
      printId: normalizeCommanderArtId(card.id),
      artRef: "",
      art: card.art,
      setLabel: "Default"
    }]
    : [];

  const cleanName = `${card.name || ""}`.trim();
  const printsUrl = `${card.printsUri || ""}`.trim();
  const requestUrl = printsUrl || `https://api.scryfall.com/cards/search?unique=prints&order=released&q=${encodeURIComponent(`!"${cleanName}" game:paper legal:commander is:commander`)}`;

  try {
    const response = await fetch(requestUrl);
    if (!response.ok) return fallback;
    const payload = await response.json();
    const cards = Array.isArray(payload.data) ? payload.data : [];

    const seen = new Set();
    const options = cards
      .filter(isCommanderEligibleCard)
      .map((printCard) => {
        const art = getCardArtCrop(printCard);
        if (!art || seen.has(art)) return null;
        seen.add(art);
        const setCode = `${printCard?.set || ""}`.toUpperCase();
        const collector = `${printCard?.collector_number || ""}`.trim();
        return {
          id: printCard.id || `${setCode}-${collector}-${art}`,
          printId: normalizeCommanderArtId(printCard.id),
          artRef: normalizeCommanderArtRef(`${setCode.toLowerCase()}/${collector}`),
          art,
          setLabel: [setCode, collector].filter(Boolean).join(" ")
        };
      })
      .filter(Boolean);

    if (!options.length) return fallback;
    return options;
  } catch {
    return fallback;
  }
}

async function clearPwaCacheForDebug() {
  const keepKeys = new Set([
    PROFILE_STORAGE_KEY,
    DECK_STORAGE_KEY,
    MATCH_HISTORY_STORAGE_KEY
  ]);

  try {
    const keysToRemove = [];
    for (let i = 0; i < localStorage.length; i += 1) {
      const key = localStorage.key(i);
      if (!key) continue;
      if (!keepKeys.has(key)) keysToRemove.push(key);
    }
    keysToRemove.forEach((key) => localStorage.removeItem(key));
  } catch {
    // Ignore storage cleanup errors during debug purge.
  }

  try {
    sessionStorage.clear();
  } catch {
    // Ignore session storage cleanup errors during debug purge.
  }

  if ("caches" in window) {
    const cacheKeys = await caches.keys();
    await Promise.all(cacheKeys.map((key) => caches.delete(key)));
  }

  if ("serviceWorker" in navigator) {
    const registrations = await navigator.serviceWorker.getRegistrations();
    await Promise.all(registrations.map((registration) => registration.unregister()));
  }
}

function renderSearchResults(seatIndex, cards, query = "") {
  const resultsEl = document.getElementById(`search-results-${seatIndex}`);
  if (!resultsEl) return;
  const state = ensureSetupState();
  const seat = state.seats[seatIndex];
  const cleanQuery = `${query || ""}`.trim();
  if (!cards.length) {
    if (!seat?.isAddingDeck || cleanQuery.length < 2 || !seat?.profileId) {
      resultsEl.innerHTML = "";
      return;
    }
    const isDuplicateForPlayer = profileAlreadyHasDeck(seat.profileId, cleanQuery);
    resultsEl.innerHTML = `
      <button class="search-result ${isDuplicateForPlayer ? "search-result-disabled" : ""}" data-action="create-default-search-deck" data-seat="${seatIndex}" data-deck-name="${escapeHtml(cleanQuery)}" ${isDuplicateForPlayer ? "disabled" : ""}>
        <img src="${DEFAULT_PLAYER_BACKGROUND}" alt="">
        <span class="search-result-copy">
          <span class="search-result-name-row">
            <span class="search-result-name">${escapeHtml(cleanQuery)}</span>
            <span class="search-result-badge search-result-badge-muted">Default Deck</span>
            ${isDuplicateForPlayer ? '<span class="search-result-badge search-result-badge-muted">Added</span>' : ""}
          </span>
          <span class="search-result-meta">${navigator.onLine ? "No online match found. Create locally." : "Offline mode. Create locally with default art."}</span>
        </span>
      </button>
    `;
    return;
  }
  resultsEl.innerHTML = cards.map(card => {
    const isDuplicateForPlayer = profileAlreadyHasDeck(seat?.profileId, card.name);
    return `
    <button class="search-result ${isDuplicateForPlayer ? "search-result-disabled" : ""}" data-action="select-search-card" data-seat="${seatIndex}" data-card-id="${card.id}" ${isDuplicateForPlayer ? "disabled" : ""}>
      <img src="${card.art}" alt="">
      <span class="search-result-copy">
        <span class="search-result-name-row">
          <span class="search-result-name">${card.name}</span>
          ${card.exact ? '<span class="search-result-badge">Exact</span>' : ""}
          ${isDuplicateForPlayer ? '<span class="search-result-badge search-result-badge-muted">Added</span>' : ""}
        </span>
        <span class="search-result-meta">${card.typeLine}</span>
      </span>
    </button>
  `;
  }).join("");

  state.seats[seatIndex].searchResults = cards;
}

/* =========================
   Start / Setup Screen
   ========================= */
function setupStartScreen() {
  const container = document.getElementById("player-buttons");
  const startScreen = document.getElementById("start-screen");
  if (!container || !startScreen) return;

  ensureSetupState();
  renderStartScreenBackdrop();
  renderStartSetupScreen();

  if (container.dataset.bound === "1") return;
  container.dataset.bound = "1";

  async function handleSetupActionFromEvent(event, root) {
    const btn = event.target.closest("button[data-action]");
    if (!btn) return;
    const state = ensureSetupState();
    const action = btn.dataset.action;
    const seat = Number(btn.dataset.seat);

    if (action === "set-mode") {
      state.mode = btn.dataset.mode === "magic" ? "magic" : "commander";
      if (state.mode === "magic") {
        state.playerCount = 2;
        state.matchLength = normalizeDuelMatchLength(state.matchLength);
        state.startingLife = 20;
        if (state.startingPlayerIndex > 1) state.startingPlayerIndex = 0;
      } else if (state.startingLife === 20) {
        state.startingLife = 40;
      }
      renderStartSetupScreen();
      return;
    }

    if (action === "set-player-count") {
      if (state.mode === "magic") return;
      state.playerCount = Math.min(6, Math.max(2, Number(btn.dataset.playerCount) || 4));
      state.startingPlayerIndex = Math.min(state.startingPlayerIndex, state.playerCount - 1);
      renderStartSetupScreen();
      return;
    }

    if (action === "set-match-length") {
      if (state.mode !== "magic") return;
      state.matchLength = normalizeDuelMatchLength(btn.dataset.matchLength);
      renderStartSetupScreen();
      return;
    }

    if (action === "set-life") {
      state.startingLife = Number(btn.dataset.life) || 40;
      renderStartSetupScreen();
      return;
    }

    if (action === "debug-clear-cache") {
      btn.disabled = true;
      btn.textContent = "Clearing...";
      void clearPwaCacheForDebug().finally(() => {
        window.location.reload();
      });
      return;
    }

    if (action === "open-qr") {
      state.qrOpen = true;
      state.qrView = "menu";
      state.qrStatus = "";
      state.qrInput = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "close-qr") {
      stopQrScanner();
      state.qrOpen = false;
      state.qrView = "menu";
      state.qrInput = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "back-qr-menu") {
      stopQrScanner();
      state.qrView = "menu";
      state.qrInput = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "open-qr-share") {
      await hydrateMissingDeckArtRefs({ limit: 100 });
      const transferBundle = buildQrTransferBundle(true);
      const transferPayload = encodeQrTransferPayload(transferBundle);
      const qrPayload = encodeQrTransferPayload(buildQrTransferBundle(false));
      const qrDataUrl = buildLocalQrDataUrl(qrPayload);
      const hasQrImage = !!qrDataUrl;

      state.qrOpen = true;
      state.qrView = "share";
      state.qrSharePayload = transferPayload;
      state.qrDisplayPayload = qrPayload;
      state.qrImageUrl = qrDataUrl;
      state.qrStatus = hasQrImage
        ? "Share player and deck names with a QR code. Alternatively use the text code."
        : "Data is too large for a single QR code. Use Copy/Share.";
      renderStartSetupScreen();
      return;
    }

    if (action === "copy-qr-payload") {
      const payload = `${state.qrSharePayload || ""}`.trim();
      if (!payload) return;
      try {
        await navigator.clipboard.writeText(payload);
        state.qrStatus = "Data copied.";
      } catch {
        state.qrStatus = "Copy failed.";
      }
      renderStartSetupScreen();
      return;
    }

    if (action === "native-share-qr") {
      const payload = `${state.qrSharePayload || ""}`.trim();
      if (!payload) return;
      if (!navigator.share) {
        state.qrStatus = "Native share unavailable here. Use Copy.";
        renderStartSetupScreen();
        return;
      }
      try {
        await navigator.share({
          title: "LifeX Transfer",
          text: payload
        });
      } catch {
        // User canceled or platform share failed.
      }
      return;
    }

    if (action === "open-qr-scan") {
      state.qrOpen = true;
      state.qrView = "scan";
      state.qrStatus = "Scanning...";
      state.qrInput = "";
      renderStartSetupScreen();
      void startQrScanner();
      return;
    }

    if (action === "import-qr-payload") {
      const payload = `${state.qrInput || ""}`.trim();
      if (!payload) {
        state.qrStatus = "Paste Data first.";
        renderStartSetupScreen();
        return;
      }
      const parsed = parseQrTransferPayload(payload);
      if (!parsed) {
        state.qrStatus = "Invalid Data.";
        renderStartSetupScreen();
        return;
      }
      const merged = mergeImportedTransferData(parsed);
      state.qrView = "menu";
      state.qrStatus = formatQrImportStatus(merged);
      state.qrInput = "";
      stopQrScanner();
      renderStartSetupScreen();
      return;
    }

    if (action === "open-start-logs") {
      state.step = "history";
      state.historyView = "list";
      state.historyEntryId = "";
      state.historyDeleteMode = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "resume-saved-game") {
      const resumeId = btn.dataset.resumeId || "";
      const entry = resumeSessions.find(item => item.id === resumeId);
      if (!entry?.snapshot) return;
      applyStateSnapshot(cloneStateSnapshot(entry.snapshot));
      saveState();
      return;
    }

    if (action === "back-from-history") {
      state.step = "config";
      state.historyView = "list";
      state.historyEntryId = "";
      state.historyDeleteMode = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "back-from-history-detail") {
      state.historyView = "list";
      state.historyEntryId = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "open-history-delete") {
      state.historyDeleteMode = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-history-delete") {
      state.historyDeleteMode = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-history-entry") {
      const historyId = btn.dataset.historyId || "";
      if (!historyId) return;
      state.historyView = "detail";
      state.historyEntryId = historyId;
      state.historyDeleteMode = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "delete-history-entry") {
      const historyId = btn.dataset.historyId || "";
      if (!deleteMatchHistoryEntry(historyId)) return;
      state.historyView = "list";
      state.historyEntryId = "";
      state.historyDeleteMode = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "continue-from-config") {
      state.step = "seats";
      state.showStarterPicker = false;
      state.forceDeckSelection = state.mode === "commander";
      renderStartSetupScreen();
      return;
    }

    if (action === "back-to-config") {
      state.step = "config";
      state.showStarterPicker = false;
      state.forceDeckSelection = false;
      renderStartSetupScreen();
      return;
    }

    if ((action === "apply-profile" || action === "select-profile") && Number.isInteger(seat)) {
      const profileId = action === "select-profile"
        ? (btn.dataset.profileId || "")
        : (document.querySelector(`[data-seat-profile-select="${seat}"]`)?.value || "");
      const profile = profileLibrary.find(item => item.id === profileId);
      if (!profile) return;
      if (isProfileSelectedInOtherSeat(state, profile.id, seat)) {
        alert("That player is already selected for another seat.");
        return;
      }
      markProfileAsUsed(profile.id);
      state.seats[seat].profileId = profile.id;
      state.seats[seat].profileName = profile.name;
      state.seats[seat].deckId = "";
      state.seats[seat].deckName = "";
      state.seats[seat].cardName = "";
      state.seats[seat].borrowedFromProfileId = "";
      state.seats[seat].borrowedFromProfileName = "";
      state.seats[seat].image = DEFAULT_PLAYER_BACKGROUND;
      state.seats[seat].isAddingProfile = false;
      state.seats[seat].newProfileName = "";
      state.seats[seat].isAddingDeck = false;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].searchResults = [];
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "add-profile" && Number.isInteger(seat)) {
      state.seats[seat].isAddingProfile = true;
      state.seats[seat].isDeletingProfile = false;
      state.seats[seat].newProfileName = "";
      state.seats[seat].hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-add-profile" && Number.isInteger(seat)) {
      state.seats[seat].isAddingProfile = false;
      state.seats[seat].newProfileName = "";
      state.seats[seat].hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-delete-profile" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingProfile = true;
      state.seats[seat].isAddingProfile = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-delete-profile" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingProfile = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "delete-profile" && Number.isInteger(seat)) {
      const profileId = btn.dataset.profileId || "";
      if (!deleteProfileById(profileId)) return;
      state.seats[seat].isDeletingProfile = false;
      state.forceDeckSelection = hasAnySelectedProfile(state);
      renderStartSetupScreen();
      return;
    }

    if (action === "create-profile" && Number.isInteger(seat)) {
      const name = (state.seats[seat].newProfileName || "").trim();
      if (!name) return;
      if (profileNameExists(name)) {
        state.seats[seat].hasDuplicateProfileName = true;
        renderStartSetupScreen();
        return;
      }
      const profile = {
        id: `${Date.now()}-${Math.random().toString(16).slice(2, 8)}`,
        name,
        lastUsedAt: Date.now()
      };
      profileLibrary.unshift(profile);
      profileLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
      saveProfileLibrary();
      state.seats[seat].profileId = profile.id;
      state.seats[seat].profileName = profile.name;
      state.seats[seat].deckId = "";
      state.seats[seat].deckName = "";
      state.seats[seat].cardName = "";
      state.seats[seat].borrowedFromProfileId = "";
      state.seats[seat].borrowedFromProfileName = "";
      state.seats[seat].image = DEFAULT_PLAYER_BACKGROUND;
      state.seats[seat].isAddingProfile = false;
      state.seats[seat].newProfileName = "";
      state.seats[seat].hasDuplicateProfileName = false;
      state.seats[seat].isDeletingProfile = false;
      state.seats[seat].isAddingDeck = false;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].searchResults = [];
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-borrow-deck" && Number.isInteger(seat)) {
      state.seats[seat].isBorrowingDeck = true;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].isAddingDeck = false;
      state.seats[seat].isDeletingDeck = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-borrow-deck" && Number.isInteger(seat)) {
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "back-borrow-profile" && Number.isInteger(seat)) {
      state.seats[seat].borrowProfileId = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "select-borrow-profile" && Number.isInteger(seat)) {
      const profileId = btn.dataset.profileId || "";
      state.seats[seat].borrowProfileId = profileId;
      renderStartSetupScreen();
      return;
    }

    if (action === "select-deck" && Number.isInteger(seat)) {
      const deckId = btn.dataset.deckId || "";
      if (isDeckSelectedInOtherSeat(state, deckId, seat)) return;
      const deck = markDeckAsUsed(deckId);
      if (!deck) return;
      const expectedOwnerId = state.seats[seat].isBorrowingDeck
        ? state.seats[seat].borrowProfileId
        : state.seats[seat].profileId;
      if (deck.ownerProfileId !== expectedOwnerId) return;
      state.seats[seat].deckId = deck.id;
      state.seats[seat].deckName = deck.deckName || "";
      state.seats[seat].cardName = deck.cardName || "";
      state.seats[seat].artId = normalizeCommanderArtId(deck.artId);
      state.seats[seat].borrowedFromProfileId = state.seats[seat].isBorrowingDeck ? expectedOwnerId : "";
      state.seats[seat].borrowedFromProfileName = state.seats[seat].isBorrowingDeck
        ? (profileLibrary.find(item => item.id === expectedOwnerId)?.name || "")
        : "";
      state.seats[seat].image = deck.image || DEFAULT_PLAYER_BACKGROUND;
      state.seats[seat].isAddingDeck = false;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].searchQuery = "";
      state.seats[seat].searchResults = [];
      state.seats[seat].pendingSearchCard = null;
      state.seats[seat].searchArtOptions = [];
      state.seats[seat].isLoadingArtOptions = false;
      state.forceDeckSelection = false;
      if (!refreshSetupSeatOverlay(seat)) {
        renderStartSetupScreen();
      }
      return;
    }

    if (action === "open-delete-deck" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingDeck = true;
      state.seats[seat].isAddingDeck = false;
      if (!refreshSetupSeatOverlay(seat)) {
        renderStartSetupScreen();
      }
      return;
    }

    if (action === "close-delete-deck" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingDeck = false;
      if (!refreshSetupSeatOverlay(seat)) {
        renderStartSetupScreen();
      }
      return;
    }

    if (action === "delete-deck" && Number.isInteger(seat)) {
      const deckId = btn.dataset.deckId || "";
      if (!deleteDeckById(deckId)) return;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.forceDeckSelection = !allSetupSeatsReady(state);
      renderStartSetupScreen();
      return;
    }

    if (action === "add-deck" && Number.isInteger(seat)) {
      if (!state.seats[seat].profileId) return;
      state.seats[seat].isAddingDeck = true;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].searchQuery = "";
      state.seats[seat].pendingSearchCard = null;
      state.seats[seat].searchArtOptions = [];
      state.seats[seat].isLoadingArtOptions = false;
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-add-deck" && Number.isInteger(seat)) {
      state.seats[seat].isAddingDeck = false;
      state.seats[seat].isDeletingDeck = false;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.seats[seat].searchQuery = "";
      state.seats[seat].searchResults = [];
      state.seats[seat].pendingSearchCard = null;
      state.seats[seat].searchArtOptions = [];
      state.seats[seat].isLoadingArtOptions = false;
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "create-default-search-deck" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      if (!seatState.profileId || !seatState.isAddingDeck) return;
      const requestedName = `${btn.dataset.deckName || seatState.searchQuery || ""}`.trim();
      if (requestedName.length < 2) return;
      if (profileAlreadyHasDeck(seatState.profileId, requestedName)) {
        return;
      }
      const deck = {
        id: `${Date.now()}-${Math.random().toString(16).slice(2, 8)}`,
        mode: "commander",
        ownerProfileId: seatState.profileId,
        deckName: requestedName,
        cardName: requestedName,
        artId: "",
        image: DEFAULT_PLAYER_BACKGROUND,
        lastUsedAt: Date.now()
      };
      deckLibrary.unshift(deck);
      saveDeckLibrary();
      seatState.deckId = deck.id;
      seatState.deckName = deck.deckName;
      seatState.cardName = deck.cardName;
      seatState.artId = "";
      seatState.borrowedFromProfileId = "";
      seatState.borrowedFromProfileName = "";
      seatState.image = deck.image;
      seatState.isAddingDeck = false;
      seatState.isDeletingDeck = false;
      seatState.isBorrowingDeck = false;
      seatState.borrowProfileId = "";
      seatState.searchQuery = "";
      seatState.searchResults = [];
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      state.forceDeckSelection = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "select-search-card" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      if (!seatState.profileId || !seatState.isAddingDeck) return;
      const id = btn.dataset.cardId;
      const match = (seatState.searchResults || []).find(card => card.id === id);
      if (!match) return;
      if (profileAlreadyHasDeck(seatState.profileId, match.name)) {
        return;
      }
      seatState.pendingSearchCard = {
        id: match.id,
        name: match.name,
        art: match.art,
        printsUri: match.printsUri || ""
      };
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = true;
      renderStartSetupScreen();
      const selectedCardId = seatState.pendingSearchCard.id;
      const artOptions = await fetchCommanderPrintArts(seatState.pendingSearchCard);
      if (!seatState.isAddingDeck) return;
      if (!seatState.pendingSearchCard || seatState.pendingSearchCard.id !== selectedCardId) return;
      if ((artOptions || []).length <= 1) {
        const chosenArt = artOptions?.[0]?.art || seatState.pendingSearchCard.art || "";
        const deck = {
          id: `${Date.now()}-${Math.random().toString(16).slice(2, 8)}`,
          mode: "commander",
          ownerProfileId: seatState.profileId,
          deckName: seatState.pendingSearchCard.name,
          cardName: seatState.pendingSearchCard.name,
          artId: normalizeCommanderArtId(artOptions?.[0]?.printId || seatState.pendingSearchCard.id),
          artRef: normalizeCommanderArtRef(artOptions?.[0]?.artRef),
          image: chosenArt,
          lastUsedAt: Date.now()
        };
        void warmCommanderImageCacheUrls([deck.image]);
        deckLibrary.unshift(deck);
        saveDeckLibrary();
        seatState.deckId = deck.id;
        seatState.deckName = deck.deckName;
        seatState.cardName = deck.cardName;
        seatState.artId = deck.artId;
        seatState.borrowedFromProfileId = "";
        seatState.borrowedFromProfileName = "";
        seatState.image = deck.image;
        seatState.isAddingDeck = false;
        seatState.isDeletingDeck = false;
        seatState.isBorrowingDeck = false;
        seatState.borrowProfileId = "";
        seatState.searchQuery = "";
        seatState.searchResults = [];
        seatState.pendingSearchCard = null;
        seatState.searchArtOptions = [];
        seatState.isLoadingArtOptions = false;
        state.forceDeckSelection = false;
        renderStartSetupScreen();
        return;
      }
      seatState.searchArtOptions = artOptions;
      seatState.isLoadingArtOptions = false;
      void warmCommanderImageCacheUrls(artOptions.map(option => option.art));
      renderStartSetupScreen();
      return;
    }

    if (action === "back-to-search-results" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "select-search-art" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      if (!seatState.profileId || !seatState.isAddingDeck || !seatState.pendingSearchCard) return;
      if (profileAlreadyHasDeck(seatState.profileId, seatState.pendingSearchCard.name)) {
        return;
      }
      const artId = btn.dataset.artId || "";
      const selectedArt = (seatState.searchArtOptions || []).find(option => option.id === artId);
      const fallbackArt = seatState.pendingSearchCard.art || "";
      const deck = {
        id: `${Date.now()}-${Math.random().toString(16).slice(2, 8)}`,
        mode: "commander",
        ownerProfileId: seatState.profileId,
        deckName: seatState.pendingSearchCard.name,
        cardName: seatState.pendingSearchCard.name,
        artId: normalizeCommanderArtId(selectedArt?.printId || seatState.pendingSearchCard.id),
        artRef: normalizeCommanderArtRef(selectedArt?.artRef),
        image: selectedArt?.art || fallbackArt,
        lastUsedAt: Date.now()
      };
      void warmCommanderImageCacheUrls([deck.image]);
      deckLibrary.unshift(deck);
      saveDeckLibrary();
      seatState.deckId = deck.id;
      seatState.deckName = deck.deckName;
      seatState.cardName = deck.cardName;
      seatState.artId = deck.artId;
      seatState.borrowedFromProfileId = "";
      seatState.borrowedFromProfileName = "";
      seatState.image = deck.image;
      seatState.isAddingDeck = false;
      seatState.isDeletingDeck = false;
      seatState.isBorrowingDeck = false;
      seatState.borrowProfileId = "";
      seatState.searchQuery = "";
      seatState.searchResults = [];
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      state.forceDeckSelection = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "reset-seat" && Number.isInteger(seat)) {
      state.seats[seat] = getDefaultSeatState(seat);
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "go-back-seat" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.deckId = "";
      seatState.deckName = "";
      seatState.cardName = "";
      seatState.artId = "";
      seatState.image = DEFAULT_PLAYER_BACKGROUND;
      seatState.isAddingDeck = false;
      seatState.isDeletingDeck = false;
      seatState.searchQuery = "";
      seatState.searchResults = [];
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      state.forceDeckSelection = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "go-back-profile-seat" && Number.isInteger(seat)) {
      state.seats[seat] = getDefaultSeatState(seat);
      state.forceDeckSelection = hasAnySelectedProfile(state);
      renderStartSetupScreen();
      return;
    }

    if (action === "back-from-board-starter") {
      if (pendingDuelContinuation) {
        pendingDuelContinuation = null;
        openEndMenu(winnerIndex !== null && winnerIndex >= 0 ? winnerIndex : undefined);
        return;
      }
      state.forceDeckSelection = true;
      document.getElementById("setup-center-play")?.remove();
      document.getElementById("setup-center-back")?.remove();
      renderStartSetupScreen();
      return;
    }

    if (action === "open-starter-picker") {
      if (!allCommanderSeatsReady(state)) return;
      state.showStarterPicker = true;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-starter-picker") {
      state.showStarterPicker = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "set-starting-player" && Number.isInteger(seat)) {
      state.startingPlayerIndex = Math.min(state.playerCount - 1, Math.max(0, seat));
      renderStartSetupScreen();
      return;
    }

    if (action === "back-from-starter") {
      state.step = state.mode === "magic" ? "config" : "seats";
      state.showStarterPicker = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "back-from-duel-next-starter") {
      pendingDuelContinuation = null;
      openEndMenu(winnerIndex !== null && winnerIndex >= 0 ? winnerIndex : undefined);
      return;
    }

    if (action === "start-configured-game") {
      if (pendingDuelContinuation) {
        const continuation = pendingDuelContinuation;
        pendingDuelContinuation = null;
        quickStartGame(2, {
          mode: "magic",
          matchLength: continuation.nextSeries.matchLength,
          startingLife: state.startingLife,
          startingPlayerIndex: Math.min(1, Math.max(0, Number(state.startingPlayerIndex) || 0)),
          seats: state.seats,
          preserveDuelSeries: true,
          duelSeries: continuation.nextSeries,
          gameLog: continuation.gameLog
        });
        return;
      }

      const playerCount = state.mode === "magic" ? 2 : state.playerCount;
      if (state.mode === "commander" && !allCommanderSeatsReady(state)) {
        alert("Select profile and deck for all players first.");
        return;
      }
      console.log("Starting game setup:", {
        mode: state.mode,
        playerCount,
        startingLife: state.startingLife,
        startingPlayerIndex: state.startingPlayerIndex,
        seats: state.seats.slice(0, playerCount)
      });
      quickStartGame(playerCount, {
        mode: state.mode,
        matchLength: state.matchLength,
        startingLife: state.startingLife,
        startingPlayerIndex: state.startingPlayerIndex,
        seats: state.seats
      });
    }
  }

  container.addEventListener("click", (event) => handleSetupActionFromEvent(event, container));
  game.addEventListener("click", (event) => {
    if (!setupGridPreviewActive) return;
    handleSetupActionFromEvent(event, game);
  });

  async function handleSetupInputFromEvent(event) {
    const state = ensureSetupState();
    const qrInput = event.target.closest("[data-qr-input]");
    if (qrInput) {
      state.qrInput = qrInput.value || "";
      return;
    }

    const seatInput = event.target.closest("[data-seat-input]");
    if (seatInput) {
      const seat = Number(seatInput.dataset.seat);
      const key = seatInput.dataset.seatInput;
      if (Number.isInteger(seat) && state.seats[seat] && key) {
        state.seats[seat][key] = seatInput.value;
        if (key === "newProfileName") {
          if (state.seats[seat].hasDuplicateProfileName) {
            state.seats[seat].hasDuplicateProfileName = false;
            renderStartSetupScreen();
          }
        }
      }
      return;
    }

    const searchInput = event.target.closest("[data-seat-deck-search]");
    if (searchInput) {
      const seat = Number(searchInput.dataset.seatDeckSearch);
      if (!Number.isInteger(seat)) return;
      const query = searchInput.value || "";
      state.seats[seat].searchQuery = query;
      state.seats[seat].pendingSearchCard = null;
      state.seats[seat].searchArtOptions = [];
      state.seats[seat].isLoadingArtOptions = false;
      const token = ++scryfallSearchToken;
      const cards = await searchScryfallCards(query, { commanderOnly: true });
      if (token !== scryfallSearchToken) return;
      renderSearchResults(seat, cards, query);
    }
  }

  container.addEventListener("input", handleSetupInputFromEvent);
  game.addEventListener("input", async (event) => {
    if (!setupGridPreviewActive) return;
    await handleSetupInputFromEvent(event);
  });
}

function quickStartGame(playerCount, options = {}) {
  stopQrScanner();
  const normalizedCount = Math.min(6, Math.max(2, Number(playerCount) || 4));
  const mode = options.mode === "magic" ? "magic" : "commander";
  const matchLength = normalizeDuelMatchLength(options.matchLength);
  const configuredLife = Number(options.startingLife) || 40;
  const configuredStart = Math.min(normalizedCount - 1, Math.max(0, Number(options.startingPlayerIndex) || 0));
  const seats = Array.isArray(options.seats) ? options.seats : [];

  gameMode = mode;
  duelSeries = options.preserveDuelSeries
    ? normalizeDuelSeriesState(options.duelSeries)
    : createDefaultDuelSeriesState(matchLength);
  starting_life = configuredLife;
  hasStartedGame = true;

  // Reset full game state
  isGameOver = false;
  isPaused = false;
  selectedPlayerCount = normalizedCount;
  activePlayerIndex = configuredStart;
  turnNumber = 1;
  gameLog = options.preserveDuelSeries && Array.isArray(options.gameLog)
    ? options.gameLog
        .map(entry => ({
          game: Number.isFinite(entry?.game) && entry.game > 0 ? entry.game : 1,
          turn: Number.isFinite(entry?.turn) && entry.turn > 0 ? entry.turn : 1,
          activePlayerName: entry?.activePlayerName || "",
          tone: entry?.tone || "default",
          message: entry?.message || ""
        }))
        .filter(entry => entry.message)
    : [];
  lastEliminationCause = null;
  lastEliminationSelections = [];
  endGameSelectedCauses = [];
  resetMatchStats();

  // Reset players completely
  players.forEach((p, index) => {
    const seat = seats[index] || getDefaultSeatState(index);
    p.name = (seat.profileName || "").trim() || `Player ${index + 1}`;
    p.commander = mode === "magic" ? "" : ((seat.cardName || "").trim());
    p.commanderArtId = mode === "magic" ? "" : normalizeCommanderArtId(seat.artId);
    p.image = getSeatBackgroundImage(seat, index, mode);
    p.life = configuredLife;
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  });

  // Stop timers
  if (turnInterval) clearInterval(turnInterval);
  turnInterval = null;
  turnStartTime = null;

  // Remove saved state
  localStorage.removeItem(STORAGE_KEY);
  undoStack = [];

  // Hide all menus
  exitSetupGridPreview();
  document.getElementById("end-screen")?.classList.add("hidden");
  document.getElementById("start-screen")?.classList.add("hidden");
  document.getElementById("start-screen")?.classList.remove("setup-open");
  document.getElementById("player-buttons")?.classList.add("hidden");

  // Remove blur
  document.getElementById("game").classList.remove("blurred");

  // Show pause button again
  pauseBtn.classList.remove("hidden");
  setPauseButtonIcon(false);
  closeGameLogPanel();

  render();
  startTurnTimer(true);
  updateUndoButtonState();
  saveState();
  triggerHaptic("success");
}

function nextTurn(recordHistory = true, reason = "Pass") {
  if (recordHistory instanceof Event) {
    recordHistory = true;
    reason = "Pass";
  }
  if (isDamageMode) return;
  if (isGameOver) return;

  syncActivePlayerTimer();
  if (recordHistory) pushUndoSnapshot();
  const previousPlayerIndex = activePlayerIndex;

  let attempts = 0;

  do {

    activePlayerIndex = (activePlayerIndex + 1) % selectedPlayerCount;

    attempts++;

  } while (
    players[activePlayerIndex].life === 0 &&
    attempts < selectedPlayerCount
  );

  const wrappedToNextRound = activePlayerIndex <= previousPlayerIndex;
  if (wrappedToNextRound) {
    turnNumber += 1;
  }

  startTurnTimer(true);

  saveState();
  render();
  triggerHaptic("step");
}

function autoPassIfActivePlayerDead() {
  if (!selectedPlayerCount) return;
  if (isGameOver) return;
  if (players[activePlayerIndex].life > 0) return;
  nextTurn(false, "Auto-pass");
}

/* =========================
   Main Render + Grid Layout
   ========================= */
function render() {
  clearSeriesWinnerSeatHighlight();
  if (!selectedPlayerCount) return;
  game.dataset.players = String(selectedPlayerCount);
  document.body.dataset.players = String(selectedPlayerCount);
  game.innerHTML = "";

  const order = getPlayerOrder(selectedPlayerCount);
  // Ensure arrow layer exists
let svg = document.getElementById("damage-arrow-layer");

if (!svg) {
  svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.id = "damage-arrow-layer";
  game.appendChild(svg);
}

svg.innerHTML = "";

  order.forEach((index, seatPos) => {
    const player = players[index];
    const isJudySeat = isJudyPlayerName(player?.name);

    const div = document.createElement("div");
    div.className = "player";
    div.id = "player" + index;
    div.dataset.seatPos = String(seatPos);
    if (isJudySeat) {
      div.classList.add("judy-mode");
      applyJudyThemeVars(div);
    }

    if (index === damageSourceIndex && isDamageMode) {
      div.classList.add("damage-source");
      }

    const isActive = players[activePlayerIndex].id === player.id && player.life > 0;
    const allowSetupActiveHighlight = !setupGridPreviewActive || shouldShowSetupActiveSeat();
    const showActiveHighlight =
      isActive &&
      allowSetupActiveHighlight &&
      !(isDamageMode && damageSourceIndex !== null && damageSourceIndex !== activePlayerIndex);
    const seatRotation = getSeatRotation(selectedPlayerCount, index);
    const seatRotationRad = (seatRotation * Math.PI) / 180;
    const healRiseX = Math.sin(seatRotationRad) * 150;
    const healRiseY = -Math.cos(seatRotationRad) * 150;

    const isDead = player.life === 0;
    if (isDead) {
      div.classList.add("dead");
    }
    div.style.setProperty("--seat-rot", `${seatRotation}deg`);
    div.style.setProperty("--heal-rise-x", `${healRiseX.toFixed(2)}%`);
    div.style.setProperty("--heal-rise-y", `${healRiseY.toFixed(2)}%`);

    div.innerHTML = `
      <div class="bg"></div>
      <div class="commander-corner">
        ${getCommanderDamageMarkup(index)}
      </div>

      <div class="poison-corner ${player.poison > 0 ? "" : "is-empty"}" style="--seat-rot:${seatRotation}deg">
        <img src="./icons/Poison.svg" class="poison-icon icon-img" alt="">
        <span class="poison">${player.poison}</span>
      </div>

      <div class="info_container">
        ${renderDuelSeriesOverlay(index)}
        <div class="info_containter_center">
          ${shouldUseBoardStarterSelection() ? "" : `<div class="timer" id="timer-${index}">${getTimerLabel(index, player, isActive)}</div>`}
          <div class="life">${getDisplayLifeMarkup(player, index)}</div>
        
          <button class="pass-btn ${isActive ? "" : "hidden"}">Pass</button>
        </div>
      </div>
    `;
    


    div.addEventListener("pointerdown", (e) => {
      if (isDamageMode) return;
      if (isPaused) return;
      if (player.life === 0) return;
      if (e.target.closest(".pass-btn")) return;
      
      isDragging = true;
      dragStartIndex = index;
      dragStartX = e.clientX;
      dragStartY = e.clientY;

      damageSourceIndex = dragStartIndex;
      triggerHaptic("minimal");

      div.setPointerCapture(e.pointerId);
    });

    div.addEventListener("click", (e) => {
      if (!shouldUseBoardStarterSelection()) return;
      if (e.target.closest("button")) return;
      if (player.life === 0) return;
      const state = ensureSetupState();
      state.startingPlayerIndex = index;
      activePlayerIndex = index;
      renderStartSetupScreen();
    });

    div.addEventListener("pointerup", (e) => {
      if (!isDragging) return;


      isDragging = false;
      dragStartIndex = null;
      cleanupDamageArrow();

      const target = document.elementFromPoint(e.clientX, e.clientY);
      const targetPlayer = target?.closest(".player");

      if (targetPlayer) {
        if (targetPlayer.classList.contains("dead")) return;
        const targetId = parseInt(targetPlayer.id.replace("player", ""));

        if (targetId !== dragStartIndex) {
          damageTargetIndex = targetId;
      
        document.querySelectorAll(".player").forEach(p =>
        p.classList.remove("target-highlight")
      );

      openDamageMenu(targetId);
    }
  }

  
  dragStartIndex = null;
});

div.addEventListener("pointermove", (e) => {
  if (!isDragging) return;
  if (isDamageMode) return;
  
  const target = document.elementFromPoint(e.clientX, e.clientY);
  const targetPlayer = target?.closest(".player");

  document.querySelectorAll(".player").forEach(p =>
    p.classList.remove("target-highlight")
  );

  if (targetPlayer) {
    targetPlayer.classList.add("target-highlight");
  }


if (isDragging && dragStartIndex !== null) {

  const target = document.elementFromPoint(e.clientX, e.clientY);
  const targetPlayer = target?.closest(".player");

  if (targetPlayer) {

    const targetId = parseInt(targetPlayer.id.replace("player", ""));

    const svg = document.getElementById("damage-arrow-layer");
    svg.querySelectorAll(".damage-arrow, .damage-arrow-head, .damage-arrow-head-wrap")
   .forEach(el => el.remove());

    drawDamageArrow(dragStartIndex, e.clientX, e.clientY);
  }
}


});







    div.querySelector(".bg").style.backgroundImage = player.image ? `url(${player.image})` : "none";

    if (isActive) {
  const passBtn = div.querySelector(".pass-btn");

  if (!isDamageMode && !isPaused && !isGameOver && player.life > 0) {
    passBtn.classList.remove("hidden");
    passBtn.addEventListener("click", nextTurn);
  } else {
    passBtn.classList.add("hidden");
  }

  if (showActiveHighlight) {
    setTimeout(() => div.classList.add("active"), 10);
  }
}

    // Special grid spans
    if (selectedPlayerCount === 3 && index === 2) {
      div.style.gridColumn = "1 / -1";
      div.classList.add("seat-special-3");
    }

    if (selectedPlayerCount === 5 && index === 3) {
      div.style.gridColumn = "1 / -1";
    }

    game.appendChild(div);
  });

  updateGridLayout();
}

function updateGridLayout() {
  const count = selectedPlayerCount;

  function applyInfoContainerBox(id, deg) {
    const playerEl = document.getElementById(`player${id}`);
    const info = document.querySelector(`#player${id} .info_container`);
    if (!playerEl || !info) return;

    const rect = playerEl.getBoundingClientRect();
    const isSideRotated = Math.abs(deg) === 90;

    // Rotated seats need swapped box dimensions so menu/layout fits inside the card.
    if (isSideRotated) {
      info.style.width = `${Math.floor(rect.height)}px`;
      info.style.height = `${Math.floor(rect.width)}px`;
    } else {
      info.style.width = `${Math.floor(rect.width)}px`;
      info.style.height = `${Math.floor(rect.height)}px`;
    }
  }

  function transformPlayer(id, deg, sizePercent) {
    const info = document.querySelector(`#player${id} .info_container`);
    const bg = document.querySelector(`#player${id} .bg`);

    if (info) {
      info.style.transform = `rotate(${deg}deg)`;
      info.style.transformOrigin = "center center";
    }

    if (bg) {
      bg.style.setProperty("--rot", `${deg}deg`);
      bg.style.width = `${sizePercent}%`;
      bg.style.height = `${sizePercent}%`;
    }

    applyInfoContainerBox(id, deg);
  }

  document.querySelectorAll(".player .bg").forEach(bg => {
    bg.style.width = "";
    bg.style.height = "";
  });

  if (count === 2) {
    game.style.gridTemplateColumns = "1fr";
    game.style.gridTemplateRows = "repeat(2, 1fr)";

    transformPlayer(0, 180, 160);
    transformPlayer(1, 0, 160);
  }

  if (count === 3 || count === 4) {
    game.style.gridTemplateColumns = "repeat(2, 1fr)";
    game.style.gridTemplateRows = "repeat(2, 1fr)";

    const size = 250;

    transformPlayer(0, 90, size);
    transformPlayer(1, -90, size);

    if (count === 3) {
      transformPlayer(2, 0, 160);
    }

    if (count === 4) {
      transformPlayer(2, -90, size);
      transformPlayer(3, 90, size);
    }
  }

  if (count === 5 || count === 6) {
    game.style.gridTemplateColumns = "repeat(2, 1fr)";
    game.style.gridTemplateRows = "repeat(3, 1fr)";

    const size = 180;

    transformPlayer(0, 90, size);
    transformPlayer(1, -90, size);
    transformPlayer(2, -90, size);

    if (count === 5) {
      transformPlayer(3, 0, 130);
      transformPlayer(4, 90, size);
    }

    if (count === 6) {
      transformPlayer(3, -90, size);
      transformPlayer(4, 90, size);
      transformPlayer(5, 90, size);
    }
  }

  updateCommanderOverlayAnchors();
}

function getPlayerOrder(count) {
  if (count === 2) return [0, 1];
  if (count === 3) return [0, 1, 2];
  if (count === 4) return [0, 1, 3, 2];
  if (count === 5) return [0, 1, 4, 2, 3];
  if (count === 6) return [0, 1, 5, 2, 4, 3];

  return [...Array(count).keys()];
}

function togglePause() {
  if (selectedPlayerCount === 0) {
    renderStartSetupScreen();
    triggerHaptic("tap");
    return;
  }

  if (isDamageMode) return;
  if (isGameOver) return;

  if (!isPaused) syncActivePlayerTimer();

  isPaused = !isPaused;

  const gameScreen = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");
  createResetButton();

  if (isPaused) {
    pauseStartedAt = Date.now();
    gameScreen.classList.add("blurred");
    setPauseButtonIcon(true);
    pauseBtn.classList.add("active");
    startScreen.classList.remove("setup-open");
    startScreen.classList.remove("hidden");
    setPauseMenuControlsVisible(true);
  } else {
    if (pauseStartedAt) {
      const pausedDuration = Date.now() - pauseStartedAt;
      turnStartTime += pausedDuration;
    }

    pauseStartedAt = null;

    gameScreen.classList.remove("blurred");
    setPauseButtonIcon(false);
    pauseBtn.classList.remove("active");
    startScreen.classList.remove("setup-open");
    startScreen.classList.add("hidden");
    setPauseMenuControlsVisible(false);

    saveState();
  }

  triggerHaptic(isPaused ? "tap" : "step");
}

function openStartMenuWhenNoGame() {
  if (selectedPlayerCount !== 0) return;
  hasStartedGame = false;
  renderStartSetupScreen();
}
function startTurnTimer(reset = false) {
  if (!selectedPlayerCount) return;

  if (players[activePlayerIndex].life === 0) return;

  if (turnInterval) clearInterval(turnInterval);

  const currentPlayer = players[activePlayerIndex];

  if (reset) {
    turnStartTime = Date.now();
    currentPlayer.turnTime = 0;
    turnTotalBase = currentPlayer.totalTime || 0;
  } else {
    const savedTime = currentPlayer.turnTime || 0;
    turnStartTime = Date.now() - (savedTime * 1000);
    turnTotalBase = Math.max(0, (currentPlayer.totalTime || 0) - savedTime);
  }

  syncActivePlayerTimer();
  updateTimerDisplay();

  turnInterval = setInterval(() => {

    if (isPaused) return;

    syncActivePlayerTimer();

    updateTimerDisplay();

  }, 1000);
}

function updateCommanderOverlayAnchors() {
  if (!selectedPlayerCount) return;

  const flipHorizontalAnchor = (anchor) => {
    if (anchor === "top-left") return "top-right";
    if (anchor === "top-right") return "top-left";
    if (anchor === "bottom-left") return "bottom-right";
    if (anchor === "bottom-right") return "bottom-left";
    if (anchor === "top-rail-left") return "top-right";
    if (anchor === "top-rail-right") return "top-left";
    return anchor;
  };
  const forceTopAnchor = (anchor) => {
    if (anchor === "bottom-left") return "top-left";
    if (anchor === "bottom-right") return "top-right";
    return anchor;
  };
  const toTopRailAnchor = (anchor) => {
    if (`${anchor || ""}`.endsWith("left")) return "top-rail-left";
    if (`${anchor || ""}`.endsWith("right")) return "top-rail-right";
    return "top-rail-right";
  };

  const pauseIsVisible =
    !!pauseBtn &&
    !pauseBtn.classList.contains("hidden") &&
    pauseBtn.offsetParent !== null;
  const pauseRect = pauseIsVisible ? pauseBtn.getBoundingClientRect() : null;
  const pauseCenter = pauseRect
    ? (pauseRect.width > 0 && pauseRect.height > 0
      ? {
        x: pauseRect.left + pauseRect.width / 2,
        y: pauseRect.top + pauseRect.height / 2
      }
      : {
        x: window.innerWidth / 2,
        y: window.innerHeight / 2
      })
    : {
        x: window.innerWidth / 2,
        y: window.innerHeight / 2
      };

  const cornerDefs = [
    { key: "top-left", xProp: "left", yProp: "top" },
    { key: "top-right", xProp: "right", yProp: "top" },
    { key: "bottom-left", xProp: "left", yProp: "bottom" },
    { key: "bottom-right", xProp: "right", yProp: "bottom" }
  ];

  const activeIndices = [...Array(selectedPlayerCount).keys()];

  activeIndices.forEach((index) => {
    const playerEl = document.getElementById(`player${index}`);
    const commanderEl = playerEl?.querySelector(".commander-corner");
    const poisonEl = playerEl?.querySelector(".poison-corner");
    const overlayPlusBtn = playerEl?.querySelector(".setup-plus-btn");
    const overlayMinusBtn = playerEl?.querySelector(".setup-minus-btn");
    const overlayBorrowBtn = playerEl?.querySelector(".setup-borrow-btn");
    const overlayBackBtn = playerEl?.querySelector(".setup-seat-back-btn");
    const overlayCancelBtn = playerEl?.querySelector(".setup-icon-circle-btn");
    if (!playerEl || !commanderEl) return;
    const seatPos = Number(playerEl.dataset.seatPos || -1);

    const rect = playerEl.getBoundingClientRect();
    let best = cornerDefs[0];
    let bestDistanceSq = -1;

    cornerDefs.forEach((corner) => {
      const x = corner.xProp === "left" ? rect.left : rect.right;
      const y = corner.yProp === "top" ? rect.top : rect.bottom;
      const dx = x - pauseCenter.x;
      const dy = y - pauseCenter.y;
      const distSq = (dx * dx) + (dy * dy);
      if (distSq > bestDistanceSq) {
        bestDistanceSq = distSq;
        best = corner;
      }
    });

    commanderEl.dataset.anchor = best.key;
    if (overlayBackBtn) overlayBackBtn.dataset.anchor = best.key;
    if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = best.key;

    if (poisonEl) {
      const sideDistances = {
        left: (() => {
          const dx = rect.left - pauseCenter.x;
          const dy = rect.top + rect.height / 2 - pauseCenter.y;
          return (dx * dx) + (dy * dy);
        })(),
        right: (() => {
          const dx = rect.right - pauseCenter.x;
          const dy = rect.top + rect.height / 2 - pauseCenter.y;
          return (dx * dx) + (dy * dy);
        })(),
        top: (() => {
          const dx = rect.left + rect.width / 2 - pauseCenter.x;
          const dy = rect.top - pauseCenter.y;
          return (dx * dx) + (dy * dy);
        })(),
        bottom: (() => {
          const dx = rect.left + rect.width / 2 - pauseCenter.x;
          const dy = rect.bottom - pauseCenter.y;
          return (dx * dx) + (dy * dy);
        })()
      };

      const outsideSide =
        sideDistances[best.xProp] >= sideDistances[best.yProp] ? best.xProp : best.yProp;

      const candidateCorners =
        outsideSide === "left"
          ? [
              { key: "top-left", x: rect.left, y: rect.top },
              { key: "bottom-left", x: rect.left, y: rect.bottom }
            ]
          : outsideSide === "right"
          ? [
              { key: "top-right", x: rect.right, y: rect.top },
              { key: "bottom-right", x: rect.right, y: rect.bottom }
            ]
          : outsideSide === "top"
          ? [
              { key: "top-left", x: rect.left, y: rect.top },
              { key: "top-right", x: rect.right, y: rect.top }
            ]
          : [
              { key: "bottom-left", x: rect.left, y: rect.bottom },
              { key: "bottom-right", x: rect.right, y: rect.bottom }
            ];

      let poisonCorner = candidateCorners[0];
      let closestDistanceSq = Infinity;
      candidateCorners.forEach((corner) => {
        const dx = corner.x - pauseCenter.x;
        const dy = corner.y - pauseCenter.y;
        const distSq = (dx * dx) + (dy * dy);
        if (distSq < closestDistanceSq) {
          closestDistanceSq = distSq;
          poisonCorner = corner;
        }
      });

      poisonEl.dataset.anchor = poisonCorner.key;
      if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = poisonCorner.key;

      const isThreeSpecial = selectedPlayerCount === 3 && index === 2;
      const isFiveSpecial = selectedPlayerCount === 5 && index === 3;
      if (isThreeSpecial || isFiveSpecial) {
        if (commanderEl.dataset.anchor === "bottom-left") {
          poisonEl.dataset.anchor = "top-left";
        } else if (commanderEl.dataset.anchor === "bottom-right") {
          poisonEl.dataset.anchor = "top-right";
        }
      }

      if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = poisonEl.dataset.anchor;

      const isMiddleRowFiveSix =
        (selectedPlayerCount === 5 || selectedPlayerCount === 6) &&
        (seatPos === 2 || seatPos === 3);
      if (isMiddleRowFiveSix) {
        const isLeftMiddleSeat = seatPos === 2;
        commanderEl.dataset.anchor = isLeftMiddleSeat ? "bottom-left" : "bottom-right";
        poisonEl.dataset.anchor = isLeftMiddleSeat ? "bottom-right" : "bottom-left";
      }

      if (selectedPlayerCount === 4) {
        if (seatPos === 0) {
          commanderEl.dataset.anchor = "top-left";
          poisonEl.dataset.anchor = "top-right";
        } else if (seatPos === 1) {
          commanderEl.dataset.anchor = "top-right";
          poisonEl.dataset.anchor = "top-left";
        } else if (seatPos === 2) {
          commanderEl.dataset.anchor = "bottom-left";
          poisonEl.dataset.anchor = "bottom-right";
        } else if (seatPos === 3) {
          commanderEl.dataset.anchor = "bottom-right";
          poisonEl.dataset.anchor = "bottom-left";
        }
      }

      if (selectedPlayerCount === 3) {
        if (seatPos === 0) {
          commanderEl.dataset.anchor = "top-left";
          poisonEl.dataset.anchor = "top-right";
        } else if (seatPos === 1) {
          commanderEl.dataset.anchor = "top-right";
          poisonEl.dataset.anchor = "top-left";
        } else if (seatPos === 2) {
          commanderEl.dataset.anchor = "bottom-right";
          poisonEl.dataset.anchor = "top-right";
        }
      }

      if (selectedPlayerCount === 2) {
        if (seatPos === 0) {
          commanderEl.dataset.anchor = "top-left";
          poisonEl.dataset.anchor = "bottom-left";
        } else if (seatPos === 1) {
          commanderEl.dataset.anchor = "bottom-right";
          poisonEl.dataset.anchor = "top-right";
        }
      }

      if (selectedPlayerCount === 6) {
        if (seatPos === 4) {
          commanderEl.dataset.anchor = "top-left";
          poisonEl.dataset.anchor = "top-right";
        } else if (seatPos === 5) {
          commanderEl.dataset.anchor = "top-right";
          poisonEl.dataset.anchor = "top-left";
        }
      }

      if (overlayBackBtn) overlayBackBtn.dataset.anchor = commanderEl.dataset.anchor;
      if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = commanderEl.dataset.anchor;
      if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = poisonEl.dataset.anchor;
      if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = poisonEl.dataset.anchor;
      if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = poisonEl.dataset.anchor;

      const shouldFlipSetupControls =
        ((selectedPlayerCount === 4 || selectedPlayerCount === 3) && (seatPos === 0 || seatPos === 1));

      if (shouldFlipSetupControls) {
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = flipHorizontalAnchor(overlayBackBtn.dataset.anchor);
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = flipHorizontalAnchor(overlayCancelBtn.dataset.anchor);
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = flipHorizontalAnchor(overlayPlusBtn.dataset.anchor);
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = flipHorizontalAnchor(overlayMinusBtn.dataset.anchor);
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = flipHorizontalAnchor(overlayBorrowBtn.dataset.anchor);
      }

      const shouldForceBottomSeatBackToTop =
        selectedPlayerCount === 4 && (seatPos === 2 || seatPos === 3);
      if (shouldForceBottomSeatBackToTop) {
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = forceTopAnchor(overlayBackBtn.dataset.anchor);
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = forceTopAnchor(overlayCancelBtn.dataset.anchor);
      }

      const shouldForceMiddleFiveSixBackToTop =
        (selectedPlayerCount === 5 || selectedPlayerCount === 6) &&
        (seatPos === 2 || seatPos === 3);
      if (shouldForceMiddleFiveSixBackToTop) {
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = forceTopAnchor(overlayBackBtn.dataset.anchor);
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = forceTopAnchor(overlayCancelBtn.dataset.anchor);
      }

      let setupRailAnchor =
        overlayBorrowBtn?.dataset.anchor ||
        overlayMinusBtn?.dataset.anchor ||
        overlayPlusBtn?.dataset.anchor ||
        poisonEl.dataset.anchor;

      const shouldOpposeBackArrowRail =
        selectedPlayerCount === 2 ||
        (selectedPlayerCount === 3 && playerEl.classList.contains("seat-special-3"));

      if (shouldOpposeBackArrowRail) {
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = toTopRailAnchor(overlayPlusBtn.dataset.anchor);
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = toTopRailAnchor(overlayMinusBtn.dataset.anchor);
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = toTopRailAnchor(overlayBorrowBtn.dataset.anchor);
        setupRailAnchor =
          overlayBorrowBtn?.dataset.anchor ||
          overlayMinusBtn?.dataset.anchor ||
          overlayPlusBtn?.dataset.anchor ||
          setupRailAnchor;
      }

      if (shouldOpposeBackArrowRail && overlayBackBtn && setupRailAnchor) {
        overlayBackBtn.dataset.anchor = flipHorizontalAnchor(setupRailAnchor);
      }

      const isBottomSpecialFive = selectedPlayerCount === 5 && seatPos === 4;
      if (isBottomSpecialFive) {
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = "top-rail-right";
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = "top-rail-right";
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = "top-rail-right";
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = "top-left";
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = "top-left";
        setupRailAnchor = "top-rail-right";
      }

      playerEl.dataset.setupRailSide = `${setupRailAnchor || ""}`.endsWith("left") ? "left" : "right";
    }
  });
}

function updateTimerDisplay() {
  if (!selectedPlayerCount) return;

  const order = getPlayerOrder(selectedPlayerCount);

  order.forEach((index) => {
    const player = players[index];
    const timerEl = document.getElementById(`timer-${index}`);
    const isActive = index === activePlayerIndex && player.life > 0;

    if (timerEl) {
      timerEl.textContent = getTimerLabel(index, player, isActive);
    }
  });
}

function syncActivePlayerTimer() {
  if (!selectedPlayerCount) return;
  if (isPaused) return;
  if (turnStartTime === null) return;

  const currentPlayer = players[activePlayerIndex];
  if (!currentPlayer || currentPlayer.life === 0) return;

  const elapsed = Math.max(0, Math.floor((Date.now() - turnStartTime) / 1000));

  currentPlayer.turnTime = elapsed;
  currentPlayer.totalTime = turnTotalBase + elapsed;
}

function formatTime(seconds) {
  const mins = String(Math.floor(seconds / 60)).padStart(2, "0");
  const secs = String(seconds % 60).padStart(2, "0");
  return `${mins}:${secs}`;
}

function escapeHtml(value) {
  return `${value || ""}`
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function formatHistoryDateTime(timestamp) {
  if (!Number.isFinite(timestamp)) return "Unknown date";
  return new Intl.DateTimeFormat(undefined, {
    year: "numeric",
    month: "short",
    day: "numeric",
    hour: "2-digit",
    minute: "2-digit"
  }).format(new Date(timestamp));
}

function getDisplayLabel(value) {
  return `${value || ""}`
    .replaceAll("Non-Combat Damage", "Spell")
    .replaceAll("Non-combat", "Spell");
}

function buildMatchHistoryEntry(finalCauseLabel, finalMessage) {
  syncActivePlayerTimer();
  const endedAt = Date.now();
  const entryId = createLocalId();
  const playersSummary = players.slice(0, selectedPlayerCount).map((player, index) => ({
    name: getPlayerNameForLog(player, index),
    commander: gameMode === "magic" ? "" : getCommanderNameForLog(player),
    artId: gameMode === "magic" ? "" : normalizeCommanderArtId(player.commanderArtId),
    image: player.image || getDefaultPlayerBackground(index, gameMode),
    totalTime: player.totalTime || 0,
    finalLife: player.life || 0,
    finalPoison: player.poison || 0,
    stats: normalizeMatchStat(matchStats[index]),
    eliminationTurn: matchEliminations[index]?.turn ?? null,
    eliminationCause: matchEliminations[index]?.cause || "",
    isWinner: winnerIndex === index
  }));

  const duelMetadata = isDuelMode()
    ? {
      duelSeriesId: typeof duelSeries?.seriesId === "string" ? duelSeries.seriesId : "",
      duelMatchLength: normalizeDuelMatchLength(duelSeries?.matchLength),
      duelGameNumber: Math.max(1, getCompletedDuelGamesCount()),
      duelWins: [duelSeries?.wins?.[0] || 0, duelSeries?.wins?.[1] || 0]
    }
    : {};

  return {
    id: entryId,
    sourceEntryId: entryId,
    createdByDeviceId: deviceId,
    endedAt,
    mode: gameMode,
    playerCount: selectedPlayerCount,
    winnerIndex,
    winnerName: winnerIndex !== null && winnerIndex >= 0 ? getPlayerNameForLog(players[winnerIndex], winnerIndex) : "",
    winCause: finalCauseLabel,
    finalMessage,
    totalMatchSeconds: playersSummary.reduce((sum, player) => sum + (player.totalTime || 0), 0),
    turnCount: turnNumber,
    actionCount: gameLog.length,
    players: playersSummary,
    gameLog: gameLog.map(entry => ({
      game: Number.isFinite(entry.game) && entry.game > 0 ? entry.game : 1,
      turn: entry.turn,
      activePlayerName: entry.activePlayerName || "",
      tone: entry.tone || "default",
      message: entry.message || ""
    })),
    ...duelMetadata
  };
}

function archiveCompletedGame(finalCauseLabel, finalMessage) {
  const entry = buildMatchHistoryEntry(finalCauseLabel, finalMessage);
  matchHistory.unshift(entry);
  matchHistory = trimMatchHistoryByCommanderCap(matchHistory);
  saveMatchHistory();
}

function deleteMatchHistoryEntry(entryId) {
  if (!entryId) return false;
  if (entryId.startsWith("series:")) {
    const seriesId = entryId.slice("series:".length);
    if (!seriesId) return false;
    const before = matchHistory.length;
    matchHistory = matchHistory.filter(entry => `${entry?.duelSeriesId || ""}` !== seriesId);
    if (matchHistory.length === before) return false;
    saveMatchHistory();
    return true;
  }
  const index = matchHistory.findIndex(entry => entry.id === entryId);
  if (index === -1) return false;
  matchHistory.splice(index, 1);
  saveMatchHistory();
  return true;
}

function getHistoryGroupScore(entries) {
  const wins = [0, 0];
  (Array.isArray(entries) ? entries : []).forEach((entry) => {
    if (entry?.winnerIndex === 0 || entry?.winnerIndex === 1) {
      wins[entry.winnerIndex] += 1;
    }
  });
  return wins;
}

function buildHistoryGroups() {
  const groups = [];
  const groupedSeriesIds = new Set();

  for (const entry of matchHistory) {
    const isDuelSeriesEntry = (entry?.mode === "magic")
      && normalizeDuelMatchLength(entry?.duelMatchLength) > 1
      && typeof entry?.duelSeriesId === "string"
      && entry.duelSeriesId.trim();

    if (!isDuelSeriesEntry) {
      groups.push({
        id: entry.id,
        type: "single",
        entry
      });
      continue;
    }

    const seriesId = entry.duelSeriesId.trim();
    if (groupedSeriesIds.has(seriesId)) continue;
    groupedSeriesIds.add(seriesId);

    const seriesEntries = matchHistory
      .filter(item => `${item?.duelSeriesId || ""}`.trim() === seriesId)
      .slice()
      .sort((a, b) => {
        const aGame = Number(a?.duelGameNumber) || 0;
        const bGame = Number(b?.duelGameNumber) || 0;
        if (aGame && bGame) return aGame - bGame;
        return (a?.endedAt || 0) - (b?.endedAt || 0);
      });

    const latestEntry = seriesEntries[seriesEntries.length - 1] || entry;
    groups.push({
      id: `series:${seriesId}`,
      type: "duel-series",
      entries: seriesEntries,
      latestEntry
    });
  }

  return groups;
}

function renderHistoryDuelSeriesDetail(group) {
  const entries = Array.isArray(group?.entries) ? group.entries : [];
  const latestEntry = group?.latestEntry || entries[entries.length - 1];
  if (!latestEntry) return "";

  const wins = getHistoryGroupScore(entries);
  const gameRows = entries.map((entry, index) => {
    const gameNum = Number(entry?.duelGameNumber) || (index + 1);
    return `
      <div class="history-series-game-row">
        <div class="history-series-game-title">Game ${gameNum}</div>
        <div class="history-final-line history-winreason-top">${escapeHtml(getDisplayLabel(entry?.finalMessage || ""))}</div>
        <div class="history-entry-body history-entry-body-static">
          <div class="history-overview-grid">
            <div><span>Total Time</span><strong>${escapeHtml(formatTime(entry.totalMatchSeconds || 0))}</strong></div>
            <div><span>Winner</span><strong>${escapeHtml(entry.winnerName || "No Winner")}</strong></div>
            <div><span>Won By</span><strong>${escapeHtml(getDisplayLabel(entry.winCause || "Unknown"))}</strong></div>
            <div><span>Turns</span><strong>${escapeHtml(String(entry.turnCount || 0))}</strong></div>
            <div><span>Mode</span><strong>${escapeHtml(modeLabel(entry.mode))}</strong></div>
            <div><span>Actions</span><strong>${escapeHtml(String(entry.actionCount || 0))}</strong></div>
          </div>
          <div class="history-player-grid">
            ${(entry.players || []).map(player => `
              <div class="history-player-card ${player.isWinner ? "is-winner" : ""}">
                <div class="history-player-header">
                  <div class="history-player-art">
                    <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
                  </div>
                  <div class="history-player-copy">
                    <h4>${escapeHtml(player.name)}</h4>
                    ${entry.mode === "magic" ? "" : `<div>${escapeHtml(player.commander)}</div>`}
                  </div>
                </div>
                <div class="history-stat-grid">
                  <div><span>Turn Time</span><strong>${escapeHtml(formatTime(player.totalTime || 0))}</strong></div>
                  <div><span>Total Damage</span><strong>${escapeHtml(String(player.stats?.damageDealt || 0))}</strong></div>
                  <div><span>Commander</span><strong>${escapeHtml(String(player.stats?.commanderDamageDealt || 0))}</strong></div>
                  <div><span>Poison</span><strong>${escapeHtml(String(player.stats?.poisonDealt || 0))}</strong></div>
                  <div><span>Healing</span><strong>${escapeHtml(String(player.stats?.healingDone || 0))}</strong></div>
                  <div><span>Final Life</span><strong>${escapeHtml(String(player.finalLife || 0))}</strong></div>
                  <div><span>Died Turn</span><strong>${player.isWinner ? "-" : escapeHtml(player.eliminationTurn ? String(player.eliminationTurn) : "-")}</strong></div>
                  <div><span>Died By</span><strong>${player.isWinner ? "-" : escapeHtml(getDisplayLabel(player.eliminationCause || "-"))}</strong></div>
                </div>
              </div>
            `).join("")}
          </div>
        </div>
      </div>
    `;
  }).join("");

  return `
    <div class="setup-panel setup-panel-wide history-detail-panel">
      <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history-detail" aria-label="Back">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
      <h2>Game History</h2>
      <div class="history-detail-shell">
        <div class="history-summary-copy history-summary-copy-detail">
          <div class="history-summary-names">${latestEntry.players.map(player => escapeHtml(player.name)).join(" | ")}</div>
          <div class="history-summary-date">${escapeHtml(formatHistoryDateTime(latestEntry.endedAt))}</div>
        </div>
        <div class="history-series-score">${wins[0]} - ${wins[1]}</div>
        <div class="history-series-list">
          ${gameRows}
        </div>
      </div>
    </div>
  `;
}

function renderHistoryEntryDetail(entry) {
  if (!entry) return "";
  return `
    <div class="setup-panel setup-panel-wide history-detail-panel">
      <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history-detail" aria-label="Back">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
      <h2>Game History</h2>
      <div class="history-detail-shell">
        <div class="history-summary-copy history-summary-copy-detail">
          <div class="history-summary-names">${entry.players.map(player => escapeHtml(player.name)).join(" | ")}</div>
          <div class="history-summary-date">${escapeHtml(formatHistoryDateTime(entry.endedAt))}</div>
        </div>
        <div class="history-summary-commanders">
          ${entry.players.map(player => `
            <div class="history-commander-thumb ${player.isWinner ? "is-winner" : ""}">
              <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
            </div>
          `).join("")}
        </div>
        <div class="history-final-line history-winreason-top">${escapeHtml(getDisplayLabel(entry.finalMessage || ""))}</div>
        <div class="history-entry-body history-entry-body-static">
          <div class="history-overview-grid">
            <div><span>Total Time</span><strong>${escapeHtml(formatTime(entry.totalMatchSeconds || 0))}</strong></div>
            <div><span>Winner</span><strong>${escapeHtml(entry.winnerName || "No Winner")}</strong></div>
            <div><span>Won By</span><strong>${escapeHtml(getDisplayLabel(entry.winCause || "Unknown"))}</strong></div>
            <div><span>Turns</span><strong>${escapeHtml(String(entry.turnCount || 0))}</strong></div>
            <div><span>Mode</span><strong>${escapeHtml(modeLabel(entry.mode))}</strong></div>
            <div><span>Actions</span><strong>${escapeHtml(String(entry.actionCount || 0))}</strong></div>
          </div>
          <div class="history-player-grid">
            ${entry.players.map(player => `
              <div class="history-player-card ${player.isWinner ? "is-winner" : ""}">
                <div class="history-player-header">
                  <div class="history-player-art">
                    <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
                  </div>
                  <div class="history-player-copy">
                    <h4>${escapeHtml(player.name)}</h4>
                    ${entry.mode === "magic" ? "" : `<div>${escapeHtml(player.commander)}</div>`}
                  </div>
                </div>
                <div class="history-stat-grid">
                  <div><span>Turn Time</span><strong>${escapeHtml(formatTime(player.totalTime || 0))}</strong></div>
                  <div><span>Total Damage</span><strong>${escapeHtml(String(player.stats?.damageDealt || 0))}</strong></div>
                  <div><span>Commander</span><strong>${escapeHtml(String(player.stats?.commanderDamageDealt || 0))}</strong></div>
                  <div><span>Poison</span><strong>${escapeHtml(String(player.stats?.poisonDealt || 0))}</strong></div>
                  <div><span>Healing</span><strong>${escapeHtml(String(player.stats?.healingDone || 0))}</strong></div>
                  <div><span>Final Life</span><strong>${escapeHtml(String(player.finalLife || 0))}</strong></div>
                  <div><span>Died Turn</span><strong>${player.isWinner ? "-" : escapeHtml(player.eliminationTurn ? String(player.eliminationTurn) : "-")}</strong></div>
                  <div><span>Died By</span><strong>${player.isWinner ? "-" : escapeHtml(getDisplayLabel(player.eliminationCause || "-"))}</strong></div>
                </div>
              </div>
            `).join("")}
          </div>
        </div>
      </div>
    </div>
  `;
}

function renderStartHistoryScreen() {
  const state = ensureSetupState();
  const groups = buildHistoryGroups();
  const selectedGroup = groups.find(group => group.id === state.historyEntryId) || null;
  if (state.historyView === "detail" && selectedGroup) {
    if (selectedGroup.type === "duel-series") {
      return renderHistoryDuelSeriesDetail(selectedGroup);
    }
    return renderHistoryEntryDetail(selectedGroup.entry);
  }

  const entriesMarkup = groups.length
    ? groups.map(group => {
      const entry = group.type === "duel-series" ? group.latestEntry : group.entry;
      const showDuelBestOfChip = entry?.mode === "magic";
      const duelBestOfChip = showDuelBestOfChip
        ? ` <span class="history-series-chip">Bo${normalizeDuelMatchLength(entry.duelMatchLength)}</span>`
        : "";
      return `
      <button class="history-list-entry ${state.historyDeleteMode ? "is-delete-mode" : ""}" data-action="${state.historyDeleteMode ? "delete-history-entry" : "open-history-entry"}" data-history-id="${group.id}">
        <div class="history-summary-copy">
          <div class="history-summary-names">${entry.players.map(player => escapeHtml(player.name)).join(" | ")}${duelBestOfChip}</div>
          <div class="history-summary-date">${escapeHtml(formatHistoryDateTime(entry.endedAt))}</div>
        </div>
        <div class="history-summary-commanders">
          ${entry.players.map(player => `
            <div class="history-commander-thumb ${player.isWinner ? "is-winner" : ""}">
              <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
            </div>
          `).join("")}
        </div>
      </button>
    `;
    }).join("")
    : `<div class="history-empty">No completed games yet.</div>`;

  return `
    <div class="setup-panel setup-panel-wide history-list-panel">
      <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history" aria-label="Back" ${state.historyDeleteMode ? "disabled" : ""}>
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
      <button class="setup-minus-btn history-delete-btn ${state.historyDeleteMode ? "active" : ""}" data-action="${state.historyDeleteMode ? "close-history-delete" : "open-history-delete"}" aria-label="Delete log mode">-</button>
      <h2>Game History</h2>
      <div class="history-list">
        ${entriesMarkup}
      </div>
    </div>
  `;
}

function renderStartHistoryStep() {
  const entriesMarkup = matchHistory.length
    ? matchHistory.map(entry => `
      <details class="history-entry">
        <summary class="history-entry-summary">
          <div class="history-summary-copy">
            <div class="history-summary-names">${entry.players.map(player => escapeHtml(player.name)).join(" · ")}</div>
            <div class="history-summary-date">${escapeHtml(formatHistoryDateTime(entry.endedAt))}</div>
          </div>
          <div class="history-summary-commanders">
            ${entry.players.map(player => `
              <div class="history-commander-thumb ${player.isWinner ? "is-winner" : ""}">
                <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
              </div>
            `).join("")}
          </div>
        </summary>
        <div class="history-entry-body">
          <div class="history-overview-grid">
            <div><span>Total Time</span><strong>${escapeHtml(formatTime(entry.totalMatchSeconds || 0))}</strong></div>
            <div><span>Winner</span><strong>${escapeHtml(entry.winnerName || "No Winner")}</strong></div>
            <div><span>Won By</span><strong>${escapeHtml(getDisplayLabel(entry.winCause || "Unknown"))}</strong></div>
            <div><span>Turns</span><strong>${escapeHtml(String(entry.turnCount || 0))}</strong></div>
            <div><span>Mode</span><strong>${escapeHtml(modeLabel(entry.mode))}</strong></div>
            <div><span>Actions</span><strong>${escapeHtml(String(entry.actionCount || 0))}</strong></div>
          </div>
          <div class="history-player-grid">
            ${entry.players.map(player => `
              <div class="history-player-card ${player.isWinner ? "is-winner" : ""}">
                <div class="history-player-header">
                  <div class="history-player-art">
                    <img src="${escapeHtml(player.image)}" alt="${escapeHtml(player.commander)}">
                  </div>
                  <div class="history-player-copy">
                    <h4>${escapeHtml(player.name)}</h4>
                    <div>${escapeHtml(player.commander)}</div>
                  </div>
                </div>
                <div class="history-stat-grid">
                  <div><span>Turn Time</span><strong>${escapeHtml(formatTime(player.totalTime || 0))}</strong></div>
                  <div><span>Total Damage</span><strong>${escapeHtml(String(player.stats?.damageDealt || 0))}</strong></div>
                  <div><span>Commander</span><strong>${escapeHtml(String(player.stats?.commanderDamageDealt || 0))}</strong></div>
                  <div><span>Poison</span><strong>${escapeHtml(String(player.stats?.poisonDealt || 0))}</strong></div>
                  <div><span>Healing</span><strong>${escapeHtml(String(player.stats?.healingDone || 0))}</strong></div>
                  <div><span>Final Life</span><strong>${escapeHtml(String(player.finalLife || 0))}</strong></div>
                </div>
              </div>
            `).join("")}
          </div>
          <div class="history-final-line">${escapeHtml(entry.finalMessage || "")}</div>
        </div>
      </details>
    `).join("")
    : `<div class="history-empty">No completed games yet.</div>`;

  return `
    <div class="setup-panel setup-panel-wide">
      <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history" aria-label="Back">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
      <h2>Game History</h2>
      <div class="history-list">
        ${entriesMarkup}
      </div>
    </div>
  `;
}

function getTimerLabel(index, player, isActive) {
  const timeLabel = formatTime(isActive ? (player.turnTime || 0) : (player.totalTime || 0));
  return isActive ? `Turn ${turnNumber} - ${timeLabel}` : timeLabel;
}

function getLifeMarkup(player) {
  return `${player.life}${player.monarch ? '<img src="./icons/Monarch.svg" class="monarch-icon icon-img" aria-label="Monarch" alt="Monarch">' : ""}`;
}

function getDisplayLifeMarkup(player, index) {
  if (shouldUseBoardStarterSelection() && index === activePlayerIndex) {
    return `
      <span class="starting-player-label">
        <span>Starting</span>
        <span>Player</span>
      </span>
    `;
  }
  return getLifeMarkup(player);
}

function setMonarchHolder(playerIndex) {
  players.forEach((p, idx) => {
    p.monarch = idx === playerIndex;
  });
}

function getNextAlivePlayerIndex(fromIndex) {
  if (!selectedPlayerCount) return -1;
  for (let step = 1; step <= selectedPlayerCount; step++) {
    const idx = (fromIndex + step) % selectedPlayerCount;
    if (players[idx] && players[idx].life > 0) return idx;
  }
  return -1;
}

function getCommanderNameForLog(player) {
  const commanderName = (player?.commander || "").trim();
  return commanderName || "Unknown Commander";
}

function getPlayerNameForLog(player, fallbackIndex) {
  const fallback = Number.isInteger(fallbackIndex) ? `Player ${fallbackIndex + 1}` : "Unknown Player";
  const playerName = (player?.name || "").trim();
  return playerName || fallback;
}

function getPlayerLogLabel(index, { includeCommander = false } = {}) {
  const player = players[index];
  const playerName = getPlayerNameForLog(player, index);
  if (!includeCommander) return playerName;

  const commanderName = getCommanderNameForLog(player);
  return `${playerName} (${commanderName})`;
}

function addGameLogEntry(entry) {
  if (!entry || !entry.message) return;

  gameLog.unshift({
    game: Number.isFinite(entry.game) && entry.game > 0
      ? entry.game
      : (isDuelMode() ? Math.max(1, duelSeries.currentGame) : 1),
    turn: Number.isFinite(entry.turn) && entry.turn > 0 ? entry.turn : turnNumber,
    activePlayerName: entry.activePlayerName || getPlayerNameForLog(players[activePlayerIndex], activePlayerIndex),
    tone: entry.tone || "default",
    message: entry.message
  });

  if (gameLog.length > MAX_GAME_LOG_ENTRIES) {
    gameLog.length = MAX_GAME_LOG_ENTRIES;
  }

  renderGameLogPanel();
  renderEndGameLogPanel();
}

function getGameLogToneFromTypes(types) {
  if (!Array.isArray(types) || types.length === 0) return "default";
  if (types.includes("Poison") || types.includes("Infect")) return "poison";
  if (types.includes("Healing") || types.includes("Lifelink")) return "healing";
  if (types.includes("Commander")) return "damage";
  return "default";
}

function getDominantDeathCause(deathEvents, types = []) {
  if (!Array.isArray(deathEvents) || deathEvents.length === 0) return null;
  const causes = deathEvents.map(e => e?.cause).filter(Boolean);

  if (causes.includes("Wincon")) return "Wincon";
  if (causes.includes("Milled")) return "Milled";
  if (causes.includes("Poison")) return "Poison";
  if (causes.includes("Commander")) return "Commander";
  if (causes.includes("Non-Combat Damage")) return "Non-Combat Damage";
  if (causes.includes("Combat Damage")) return "Combat Damage";

  // Fallback from active damage types if a generic cause slipped through.
  if (Array.isArray(types)) {
    if (types.includes("Poison") || types.includes("Infect")) return "Poison";
    if (types.includes("Commander")) return "Commander";
    if (types.includes("Milled")) return "Milled";
    if (types.includes("Wincon")) return "Wincon";
    if (types.includes("Non-combat")) return "Non-Combat Damage";
  }

  return "Combat Damage";
}

function getSeatRotation(count, index) {
  if (count === 2) {
    if (index === 0) return 180;
    if (index === 1) return 0;
  }

  if (count === 3) {
    if (index === 0) return 90;
    if (index === 1) return -90;
    if (index === 2) return 0;
  }

  if (count === 4) {
    if (index === 0) return 90;
    if (index === 1) return -90;
    if (index === 2) return -90;
    if (index === 3) return 90;
  }

  if (count === 5) {
    if (index === 0) return 90;
    if (index === 1) return -90;
    if (index === 2) return -90;
    if (index === 3) return 0;
    if (index === 4) return 90;
  }

  if (count === 6) {
    if (index === 0) return 90;
    if (index === 1) return -90;
    if (index === 2) return -90;
    if (index === 3) return -90;
    if (index === 4) return 90;
    if (index === 5) return 90;
  }

  return 0;
}

function getCommanderDamageMarkup(targetIndex) {
  if (gameMode === "magic") return "";
  const target = players[targetIndex];
  if (!target) return "";

  const seatOrder = getPlayerOrder(selectedPlayerCount);
  const hasAnyCommanderDamage = seatOrder.some(i => (target.commanderDamage?.[i] || 0) > 0);

  // Show commander panel only after this player has received commander damage.
  if (!hasAnyCommanderDamage) return "";

  const layoutClass = `commander-layout-${selectedPlayerCount}`;
  const targetSeatRotation = getSeatRotation(selectedPlayerCount, targetIndex);
  const targetFacingClass = Math.abs(targetSeatRotation) === 90 ? "target-side-facing" : "";

  const boxes = seatOrder.map((sourceIndex, seatPos) => {
    const value = target.commanderDamage?.[sourceIndex] || 0;
    const hasDamage = value > 0 ? "has-damage" : "is-zero";
    const selfSeat = sourceIndex === targetIndex ? "self-seat" : "";
    const sourceThemeClass = isJudyPlayerName(players[sourceIndex]?.name) ? "judy-source" : "normal-source";

    return `<div class="commander-box seat-pos-${seatPos} ${hasDamage} ${selfSeat} ${sourceThemeClass}" style="--seat-rot:${targetSeatRotation}deg"><span class="commander-value">${value}</span></div>`;
  }).join("");

  return `<div class="commander-counters ${layoutClass} ${targetFacingClass}">${boxes}</div>`;
}


//////////////////////////////////
//           DAMAGE             //
//////////////////////////////////
function openDamageMenu(targetIndex) {
  isDamageMode = true;
  damageSelfMode = null;
  pauseBtn.classList.add("hidden");
  render();
  triggerHaptic("tap");

  const playerDiv = document.getElementById("player" + targetIndex);
  playerDiv.classList.add("target-highlight");

  const container = playerDiv.querySelector(".info_container");

  selectedDamageTypes = [];
  damageAmount = 0;
  nonCombatAutoSelected = false;
  const actionsBelowControls =
    selectedPlayerCount === 2 ||
    (selectedPlayerCount === 3 && targetIndex === 2);
  const shouldCompactDamageFooter =
    selectedPlayerCount === 6 ||
    (selectedPlayerCount === 5 && targetIndex !== 4);
  const confirmButtonLabel = actionsBelowControls
    ? "Confirm"
    : getIconMarkup("Ok", "inline-icon");
  const confirmButtonExtraClass = actionsBelowControls ? "confirm-text-btn confirm-text-only-btn" : "";

  container.innerHTML = `
    <div class="damage-menu ${actionsBelowControls ? "actions-below" : ""}">

        <div class="damage-types">
          <div class="damage-types1">
            <button data-type="All">All</button>
            <button data-type="Others">Other</button>
            <button data-type="Non-combat">Spell</button>
            ${gameMode === "magic" ? "" : '<button data-type="Commander">Commander</button>'}
            <button data-type="Wincon">Win</button>
            <button data-type="Monarch" aria-label="Monarch">${getIconMarkup("Monarch", "inline-icon")}</button>
          </div>
          <div class="damage-types2">
            <button data-type="Lifelink">Lifelink</button>
            <button data-type="Infect">Infect</button>
            <button data-type="Healing">Heal</button>
            <button data-type="Poison">Poison</button>
            <button data-type="Milled">Milled</button>
          </div>
      </div>

      <div class="damage-footer ${shouldCompactDamageFooter ? "damage-footer-compact" : ""}">
        <div class="damage-controls">
          <button class="sign-element" onclick="changeDamage(-1)">-</button>
          <span id="damage-value">0</span>
          <button class="sign-element" onclick="changeDamage(1)">+</button>
        </div>

        <div class="damage-actions">
          <button class="confirm-btn ${confirmButtonExtraClass}" onclick="confirmDamage()" aria-label="Confirm damage">${confirmButtonLabel}</button>
          <button class="cancel-btn" onclick="cancelDamage()" aria-label="Cancel damage">${getIconMarkup("Cancel", "inline-icon")}</button>
        </div>
      </div>

    </div>
  `;

 
container.querySelectorAll(".damage-self-options button").forEach(btn => {
  btn.classList.remove("active");

  if (btn.dataset.type === damageSelfMode) {
    btn.classList.add("active");
  }
});


const minusBtn = container.querySelector(".damage-controls button:nth-child(1)");
const plusBtn  = container.querySelector(".damage-controls button:nth-child(3)");

let holdTimeout = null;
let holdInterval = null;
let isHolding = false;

function startHold(amount) {

  stopHold();

  holdTimeout = setTimeout(() => {

    isHolding = true;

    holdInterval = setInterval(() => {
      changeDamage(amount * 10);
    }, 1000);

  }, 100);

}

function stopHold() {
  clearTimeout(holdTimeout);
  clearInterval(holdInterval);

  holdTimeout = null;
  holdInterval = null;
  isHolding = false;
}

function attachHold(btn, amount) {

  btn.addEventListener("pointerdown", (e) => {
    e.preventDefault();
    startHold(amount);
  });

  btn.addEventListener("pointerup", stopHold);
  btn.addEventListener("pointercancel", stopHold);
  btn.addEventListener("pointerleave", stopHold);

}

attachHold(plusBtn, 1);
attachHold(minusBtn, -1);


container.querySelectorAll(".damage-types button").forEach(btn => {

  btn.addEventListener("click", () => {

    const type = btn.dataset.type;
    const sourceEl = document.querySelector(".player.damage-source");
    const sourceIndex = sourceEl ? Number.parseInt(sourceEl.id.replace("player", ""), 10) : null;
    const isSourceActive = Number.isInteger(sourceIndex) && sourceIndex === activePlayerIndex;

    // ---- ALL / OTHERS ----
    if (type === "All" || type === "Others") {

  // 🔁 Toggle behavior
  if (damageSelfMode === type) {
    // Unselect if already active
    damageSelfMode = null;
  } else {
    if (selectedDamageTypes.includes("Wincon") || selectedDamageTypes.includes("Monarch")) {
      updateDamageButtonUI();
      return;
    }
    damageSelfMode = type;
  }

  updateDamageButtonUI();
  return;
}

    // ---- NORMAL DAMAGE TYPES ----
    if (btn.classList.contains("disabled")) return;
    if (type === "Non-combat" && !isSourceActive) return;

    toggleDamageType(type);

  });

});

  updateDamageButtonUI();
}

function canConfirmDamage() {
  const hasSpecialMode =
    selectedDamageTypes.includes("Milled") ||
    selectedDamageTypes.includes("Wincon") ||
    selectedDamageTypes.includes("Monarch");

  if (hasSpecialMode) return true;
  return damageAmount > 0;
}

function toggleDamageType(type) {

  const soloTypes = ["Healing", "Poison", "Wincon", "Monarch"];

  if (type === "Non-combat") {
    nonCombatAutoSelected = false;
  }

  // If clicking solo type
  if (soloTypes.includes(type)) {

    // If already selected → toggle off
    if (selectedDamageTypes.includes(type)) {
      selectedDamageTypes = [];
    } else {
      if (type === "Wincon") {
        selectedDamageTypes = ["Wincon", "Non-combat"];
        nonCombatAutoSelected = true;
        damageSelfMode = null;
      } else {
        if (type === "Monarch") damageSelfMode = null;
        selectedDamageTypes = [type];
      }
    }

  } else {
    if (type === "Milled") {
      if (selectedDamageTypes.includes("Lifelink") || selectedDamageTypes.includes("Infect")) {
        updateDamageButtonUI();
        return;
      }
      if (selectedDamageTypes.includes("Milled")) {
        selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Milled");
      } else {
        selectedDamageTypes = selectedDamageTypes
          .filter(t => !["Healing", "Poison", "Commander", "Lifelink", "Infect", "Wincon", "Monarch"].includes(t));
        selectedDamageTypes.push("Milled");
      }
      updateDamageButtonUI();
      return;
    }

    // If a solo type is active → ignore
    if (selectedDamageTypes.some(t => soloTypes.includes(t))) {
      return;
    }

    // Toggle normal types
    if (selectedDamageTypes.includes(type)) {
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    } else {
      selectedDamageTypes.push(type);
    }
  }

  updateDamageButtonUI();
  triggerHaptic("tap");
}

function updateDamageButtonUI() {
  const buttons = document.querySelectorAll(".damage-types button");
  const sourceEl = document.querySelector(".player.damage-source");
  const sourceIndex = sourceEl ? Number.parseInt(sourceEl.id.replace("player", ""), 10) : null;
  const isSourceActive = Number.isInteger(sourceIndex) && sourceIndex === activePlayerIndex;
  const shouldForceNonCombat = !isSourceActive;
  const hasCurrentMonarch = players
    .slice(0, selectedPlayerCount)
    .some(p => !!p.monarch);
  const isSelf =
    sourceEl &&
    damageTargetIndex !== null &&
    sourceEl.id.replace("player", "") == damageTargetIndex;
  const milledSelected = selectedDamageTypes.includes("Milled");

  // Milled is exclusive: keep only Milled + forced Non-combat and clear mass mode.
  if (milledSelected) {
    selectedDamageTypes = selectedDamageTypes.filter(t => t === "Milled" || t === "Non-combat");
    if (!selectedDamageTypes.includes("Non-combat")) {
      selectedDamageTypes.push("Non-combat");
      nonCombatAutoSelected = true;
    }
    damageSelfMode = null;
  }

  buttons.forEach(btn => {
    const type = btn.dataset.type;
    btn.classList.remove("active", "disabled", "hidden");
    btn.style.display = "";

    // ------------------------
    // Hide All/Others if target is not self
    // ------------------------
    if (!isSelf && (type === "All" || type === "Others")) {
      btn.classList.add("hidden");
      return;
    }

    if (type === "Non-combat" && shouldForceNonCombat) {
      if (!selectedDamageTypes.includes("Non-combat")) {
        selectedDamageTypes.push("Non-combat");
      }
      nonCombatAutoSelected = true;
      btn.classList.add("active");
      return;
    }

    // Commander damage is only available when source is the active player.
    if (type === "Commander" && !isSourceActive) {
      btn.classList.add("hidden");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Commander");
      return;
    }

    if (type === "Monarch" && hasCurrentMonarch) {
      btn.classList.add("hidden");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Monarch");
      return;
    }

    // Wincon / Monarch only available when targeting self
    if (!isSelf && (type === "Wincon" || type === "Monarch")) {
      btn.classList.add("hidden");
      const hadWincon = selectedDamageTypes.includes("Wincon");
      const hadMonarch = selectedDamageTypes.includes("Monarch");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Wincon");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Monarch");
      if (hadWincon && nonCombatAutoSelected) {
        selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Non-combat");
        nonCombatAutoSelected = false;
      }
      if (hadMonarch) damageSelfMode = null;
      return;
    }

    // ------------------------
    // Self rules
    // ------------------------
    if (isSelf) {
      if (damageSelfMode === "All") {
        if (["Lifelink", "Commander"].includes(type)) btn.classList.add("disabled");
      } else if (damageSelfMode === "Others") {
        if (type === "Commander") btn.classList.add("disabled");
      } else {
        if (type === "Lifelink") btn.classList.add("disabled");
      }
    }

    // ------------------------
    // Exclusivity rules
    // ------------------------

    // Healing disables Poison and everything except Non-combat / All / Others
    if (selectedDamageTypes.includes("Healing") && type !== "Healing" && !["Non-combat", "All", "Others"].includes(type)) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Poison disables Healing and everything except Non-combat / All / Others
    if (selectedDamageTypes.includes("Poison") && type !== "Poison" && !["Non-combat", "All", "Others"].includes(type)) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Lifelink or Infect disables Healing and Poison
    if ((selectedDamageTypes.includes("Lifelink") || selectedDamageTypes.includes("Infect")) &&
        (type === "Healing" || type === "Poison")) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Wincon is exclusive
    if (selectedDamageTypes.includes("Wincon") && !["Wincon", "Non-combat"].includes(type)) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Monarch is exclusive
    if (selectedDamageTypes.includes("Monarch") && type !== "Monarch") {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Milled is exclusive and forces Non-combat.
    if (selectedDamageTypes.includes("Milled") && !["Milled", "Non-combat"].includes(type)) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    if ((selectedDamageTypes.includes("Healing") || selectedDamageTypes.includes("Poison") || selectedDamageTypes.includes("Lifelink") || selectedDamageTypes.includes("Infect")) && (type === "Milled" || type === "Wincon" || type === "Monarch")) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // Non-combat disables Commander
    if (selectedDamageTypes.includes("Non-combat") && type === "Commander") {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Commander");
    }

    // Commander disables Healing, Poison, Non-combat
    if (selectedDamageTypes.includes("Commander") && ["Healing", "Poison", "Non-combat"].includes(type)) {
      btn.classList.add("disabled");
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== type);
    }

    // ------------------------
    // NEW RULES
    // ------------------------

    // If Commander is selected, disable All and Others
    if (selectedDamageTypes.includes("Commander") && (type === "All" || type === "Others")) {
      btn.classList.add("disabled");
      if (type === damageSelfMode) damageSelfMode = null;
    }

    // Wincon / Monarch disable All and Others mode selection
    if ((selectedDamageTypes.includes("Wincon") || selectedDamageTypes.includes("Monarch")) && (type === "All" || type === "Others")) {
      btn.classList.add("disabled");
      if (type === damageSelfMode) damageSelfMode = null;
    }

    // If Others is selected, disable All, and vice versa
    if (damageSelfMode === "All" && type === "Others") btn.classList.add("disabled");
    if (damageSelfMode === "Others" && type === "All") btn.classList.add("disabled");

    // ------------------------
    // Auto-select Non-combat
    // ------------------------
    const shouldAutoSelectNonCombat =
      shouldForceNonCombat ||
      ["Healing", "Poison", "Milled", "Wincon"].some(t => selectedDamageTypes.includes(t)) ||
      damageSelfMode === "All" ||
      damageSelfMode === "Others";

    if (shouldAutoSelectNonCombat) {
      const ncBtn = Array.from(buttons).find(b => b.dataset.type === "Non-combat");
      if (ncBtn) {
        ncBtn.classList.add("active");
        if (!selectedDamageTypes.includes("Non-combat")) {
          selectedDamageTypes.push("Non-combat");
          nonCombatAutoSelected = true;
        }
      }
    } else if (nonCombatAutoSelected) {
      selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Non-combat");
      nonCombatAutoSelected = false;
    }

    // ------------------------
    // Active class
    // ------------------------
    const isSelected =
      selectedDamageTypes.includes(type) ||
      type === damageSelfMode;
    if (isSelected) btn.classList.add("active");

    // All / Others special
    if ((type === "All" || type === "Others") && damageSelfMode === type) btn.classList.add("active");
  });

  updateDamageValueColorUI();
  updateDamageControlsUI();
  updateConfirmButtonState();
  updateMassDamagePreviewUI();
}

function changeDamage(amount) {
  if (selectedDamageTypes.includes("Milled") || selectedDamageTypes.includes("Wincon") || selectedDamageTypes.includes("Monarch")) return;

  const previousAmount = damageAmount;
  damageAmount += amount;
  if (damageAmount < 0) damageAmount = 0;
  if (damageAmount === previousAmount) return;

  const el = document.getElementById("damage-value");
  if (el) el.textContent = damageAmount;

  updateDamageValueColorUI();
  updateDamageControlsUI();
  updateConfirmButtonState();
  updateMassDamagePreviewUI();
  triggerHaptic("step");
}

function closeDamageMode() {
  isDamageMode = false;
  if (isGameOver) {
    pauseBtn.classList.add("hidden");
  } else {
    pauseBtn.classList.remove("hidden");
  }

  document.body.classList.remove("damage-mode-active");

  document.querySelectorAll(".player").forEach(p => p.classList.remove("target-highlight"));
  document.querySelectorAll(".player").forEach(p => p.classList.remove("damage-source"));

  damageTargetIndex = null;
  damageAmount = 0;
  damageSelfMode = null;
  damageSourceIndex = null;
  resetMassDamagePreviewUI();
  resetDamageValueColorUI();
  updateDamageControlsUI();
  render();
}

function getDamageValueColorClass() {
  if (selectedDamageTypes.includes("Healing") || selectedDamageTypes.includes("Lifelink")) return "damage-value-healing";
  if (selectedDamageTypes.includes("Poison") || selectedDamageTypes.includes("Infect")) return "damage-value-poison";
  if (selectedDamageTypes.includes("Commander")) return "damage-value-damage";
  return "damage-value-default";
}

function updateDamageValueColorUI() {
  const el = document.getElementById("damage-value");
  if (!el) return;

  el.classList.remove("damage-value-default", "damage-value-healing", "damage-value-poison", "damage-value-damage");
  el.classList.add(getDamageValueColorClass());
}

function updateDamageControlsUI() {
  const controls = document.querySelector(".damage-controls");
  if (!controls) return;

  const disableControls =
    selectedDamageTypes.includes("Milled") ||
    selectedDamageTypes.includes("Wincon") ||
    selectedDamageTypes.includes("Monarch");

  controls.classList.toggle("disabled", disableControls);

  const valueEl = document.getElementById("damage-value");
  if (valueEl) {
    valueEl.textContent = damageAmount;
  }
}

function updateConfirmButtonState() {
  const confirmBtn = document.querySelector(".damage-actions .confirm-btn");
  if (!confirmBtn) return;

  confirmBtn.disabled = !canConfirmDamage();
}

function resetDamageValueColorUI() {
  const el = document.getElementById("damage-value");
  if (!el) return;

  el.classList.remove("damage-value-default", "damage-value-healing", "damage-value-poison", "damage-value-damage");
}

function updateMassDamagePreviewUI() {
  resetMassDamagePreviewUI();
  if (!isDamageMode) return;

  const sourceEl = document.querySelector(".player.damage-source");
  if (!sourceEl) return;

  const sourceIndex = parseInt(sourceEl.id.replace("player", ""), 10);
  if (!Number.isInteger(sourceIndex)) return;

  const activeIndices = [...Array(selectedPlayerCount).keys()];
  const winconSelected = selectedDamageTypes.includes("Wincon");
  const shouldPreview = ["All", "Others"].includes(damageSelfMode);
  const shouldWinconTarget = winconSelected;

  if (!shouldPreview && !shouldWinconTarget) return;

  let highlightTargets = [];
  if (shouldWinconTarget) {
    highlightTargets = activeIndices.filter(i => i !== sourceIndex);
  } else if (damageSelfMode === "All") {
    highlightTargets = activeIndices;
  } else {
    highlightTargets = activeIndices.filter(i => i !== sourceIndex);
  }

  const previewTargets = shouldPreview
    ? activeIndices.filter(i => i !== sourceIndex && players[i].life > 0)
    : [];
  const colorClass = getDamageValueColorClass();

  sourceEl.classList.add("source-mass-highlight");
  sourceEl.classList.toggle("source-others-preview", damageSelfMode === "Others");

  highlightTargets.forEach(i => {
    const playerEl = document.getElementById(`player${i}`);
    if (!playerEl) return;
    playerEl.classList.add("target-highlight");
  });

  if (damageSelfMode === "Others") {
    sourceEl.classList.remove("target-highlight");
  }

  previewTargets.forEach(i => {
    const playerEl = document.getElementById(`player${i}`);
    if (!playerEl) return;

    const lifeEl = playerEl.querySelector(".life");
    if (!lifeEl) return;

    playerEl.classList.add("mass-target-preview");
    lifeEl.classList.add("damage-preview-life");
    lifeEl.classList.remove("damage-value-default", "damage-value-healing", "damage-value-poison");
    lifeEl.classList.add(colorClass);
    lifeEl.textContent = damageAmount.toString();
  });
}

function resetMassDamagePreviewUI() {
  const menuPlayerEl = document.querySelector(".damage-menu")?.closest(".player");
  if (menuPlayerEl && isDamageMode) {
    menuPlayerEl.classList.add("target-highlight");
  }

  document.querySelectorAll(".player.source-mass-highlight").forEach(playerEl => {
    playerEl.classList.remove("source-mass-highlight");
  });
  document.querySelectorAll(".player.source-others-preview").forEach(playerEl => {
    playerEl.classList.remove("source-others-preview");
  });

  document.querySelectorAll(".player.mass-target-preview").forEach(playerEl => {
    playerEl.classList.remove("mass-target-preview", "target-highlight");

    const idx = parseInt(playerEl.id.replace("player", ""), 10);
    const lifeEl = playerEl.querySelector(".life");
    if (!lifeEl || !Number.isInteger(idx) || !players[idx]) return;

    lifeEl.classList.remove("damage-preview-life", "damage-value-default", "damage-value-healing", "damage-value-poison");
    lifeEl.innerHTML = getLifeMarkup(players[idx]);
  });
}

function confirmDamage() {
  if (!canConfirmDamage()) return;

  const sourceEl = document.querySelector(".player.damage-source");
  if (!sourceEl) return;

  const sourceIndex = parseInt(sourceEl.id.replace("player", ""));
  const source = players[sourceIndex];
  if (!source) return;
  const isSourceActive = sourceIndex === activePlayerIndex;

  // Hard guard: off-turn sources cannot deal commander damage and must be non-combat.
  if (!isSourceActive) {
    selectedDamageTypes = selectedDamageTypes.filter(t => t !== "Commander");
    if (!selectedDamageTypes.includes("Non-combat")) {
      selectedDamageTypes.push("Non-combat");
      nonCombatAutoSelected = true;
    }
  }

  const amount = damageAmount;
  const previousMonarchIndex = players.findIndex(p => !!p.monarch);
  const activePlayerName = getPlayerNameForLog(players[activePlayerIndex], activePlayerIndex);

  // -------------------------
  // Determine actual targets
  // -------------------------
  const types = selectedDamageTypes.length > 0
    ? selectedDamageTypes
    : [isSourceActive ? "Combat" : "Non-combat"];
  const has = t => types.includes(t);
  const hasWincon = has("Wincon");
  const hasMilled = has("Milled");
  const hasMonarch = has("Monarch");
  const activeIndices = [...Array(selectedPlayerCount).keys()];
  let targetIndices = [];

  if (hasWincon) {
    targetIndices = activeIndices.filter(i => i !== sourceIndex);
  } else
  if (damageSelfMode === "All") {
    targetIndices = activeIndices;
  } else if (damageSelfMode === "Others") {
    targetIndices = activeIndices.filter(i => i !== sourceIndex);
  } else {
    if (
      Number.isInteger(damageTargetIndex) &&
      damageTargetIndex >= 0 &&
      damageTargetIndex < selectedPlayerCount &&
      players[damageTargetIndex]
    ) {
      targetIndices = [damageTargetIndex];
    }
  }

  if (targetIndices.length === 0) return;

  pushUndoSnapshot();

  const oldStates = players.map(p => ({ life: p.life, poison: p.poison }));
  const dealsLifeDamage = !has("Healing") && !has("Poison");
  const deathEvents = [];

  console.log("=== Confirm Damage ===");
  console.log("Source:", sourceIndex, source.life, "Damage amount:", amount);
  console.log("Target indices:", targetIndices, "Types:", types);

  // -------------------------
  // Apply damage/healing
  // -------------------------
  let lifelinkHeal = 0;
  let monarchTransferTo = null;

  targetIndices.forEach(ti => {
    const target = players[ti];
    if (!target) return;
    const oldLife = oldStates[ti].life;
    const oldPoison = oldStates[ti].poison;
    const oldCommanderFromSource = target.commanderDamage?.[sourceIndex] || 0;

    if (hasMonarch) {
      setMonarchHolder(ti);
      return;
    }

    if (hasWincon || hasMilled) {
      if (oldLife > 0) {
        deathEvents.push({
          targetIndex: ti,
          cause: hasWincon ? "Wincon" : "Milled",
          tone: "damage"
        });
      }
      target.life = 0;
      return;
    }

    let lifeDamage = 0;

    // Healing
    if (has("Healing")) {
      target.life += amount;
      matchStats[sourceIndex].healingDone += amount;
      console.log(`Healing target ${ti} +${amount}, new life: ${target.life}`);
    }

    // Poison
    if (has("Poison")) {
      target.poison += amount;
      matchStats[sourceIndex].poisonDealt += amount;
      console.log(`Poison target ${ti} +${amount}, new poison: ${target.poison}`);
      if (target.poison >= 10) target.life = 0;
    }

    // Apply life damage exactly once per target.
    // Damage types (Combat/Non-combat/Lifelink/Commander/Infect) are modifiers, not extra stacks.
    if (dealsLifeDamage) lifeDamage = amount;

    // Commander
    if (has("Commander")) {
      if (!target.commanderDamage[sourceIndex]) target.commanderDamage[sourceIndex] = 0;
      target.commanderDamage[sourceIndex] += amount;
      matchStats[sourceIndex].commanderDamageDealt += amount;
      if (target.commanderDamage[sourceIndex] >= 21) target.life = 0;
    }

    // Infect
    if (has("Infect")) {
      target.poison += amount;
      matchStats[sourceIndex].poisonDealt += amount;
      if (target.poison >= 10) target.life = 0;
    }

    const stealsMonarch =
      amount > 0 &&
      sourceIndex !== ti &&
      target.monarch &&
      (has("Commander") || !has("Non-combat"));
    if (stealsMonarch) {
      monarchTransferTo = sourceIndex;
    }

    // Lifelink heals source once per damaged target.
    if (has("Lifelink") && dealsLifeDamage) {
      lifelinkHeal += amount;
    }

    target.life -= lifeDamage;
    if (lifeDamage > 0) {
      matchStats[sourceIndex].damageDealt += lifeDamage;
    }
    if (target.life < 0) target.life = 0;

    if (oldLife > 0 && target.life === 0) {
      let cause = has("Non-combat") ? "Non-Combat Damage" : "Combat Damage";
      let tone = "damage";

      const gotPoisonKill =
        (has("Poison") || has("Infect")) &&
        oldPoison < 10 &&
        target.poison >= 10;
      const gotCommanderKill =
        has("Commander") &&
        oldCommanderFromSource < 21 &&
        (target.commanderDamage?.[sourceIndex] || 0) >= 21;

      if (gotPoisonKill) {
        cause = "Poison";
        tone = "poison";
      } else if (gotCommanderKill) {
        cause = "Commander";
        tone = "damage";
      }

      deathEvents.push({
        targetIndex: ti,
        cause,
        tone
      });
    }

    console.log(`Target ${ti} final life: ${target.life}, poison: ${target.poison}, lifeDamage: ${lifeDamage}`);
  });

  const monarchDiedThisResolution =
    previousMonarchIndex >= 0 &&
    oldStates[previousMonarchIndex]?.life > 0 &&
    players[previousMonarchIndex]?.life === 0;

  if (monarchTransferTo !== null) {
    setMonarchHolder(monarchTransferTo);
  } else if (!hasMonarch && monarchDiedThisResolution) {
    let replacementMonarch = -1;

    // Edge case: if the monarch dies during their own turn, monarch passes
    // to the next alive player in turn order.
    if (previousMonarchIndex === activePlayerIndex) {
      replacementMonarch = getNextAlivePlayerIndex(activePlayerIndex);
    } else if (players[activePlayerIndex]?.life > 0) {
      replacementMonarch = activePlayerIndex;
    } else {
      replacementMonarch = getNextAlivePlayerIndex(activePlayerIndex);
    }

    setMonarchHolder(replacementMonarch);
  }

  // -------------------------
  // Heal source with Lifelink
  // -------------------------
  if (has("Lifelink") && lifelinkHeal > 0) {
    source.life += lifelinkHeal;
    matchStats[sourceIndex].healingDone += lifelinkHeal;
    console.log(`Lifelink heals source +${lifelinkHeal}, new life: ${source.life}`);
  }

  const isCommanderDamage = has("Commander");
  const sourceLabel = getPlayerLogLabel(sourceIndex, { includeCommander: isCommanderDamage });
  const logTargetLabel = targetIndices
    .map(i => getPlayerLogLabel(i))
    .join(", ");
  const logTypeLabel = getDisplayLabel(types.join(", "));
  let actionText = "";

  if (hasMonarch) {
    actionText = `${getPlayerLogLabel(sourceIndex)} became Monarch.`;
  } else if (hasWincon) {
    actionText = `${getPlayerLogLabel(sourceIndex)} used Wincon on ${logTargetLabel}.`;
  } else if (hasMilled) {
    actionText = `${getPlayerLogLabel(sourceIndex)} milled ${logTargetLabel}.`;
  } else {
    const actionVerb = has("Healing") ? "healed" : "hit";
    actionText = `${sourceLabel} ${actionVerb} ${logTargetLabel} for ${amount} (${logTypeLabel}).`;
    if (has("Lifelink") && lifelinkHeal > 0) {
      actionText += ` Lifelink +${lifelinkHeal}.`;
    }
  }

  const newMonarchIndex = players.findIndex(p => !!p.monarch);
  if (newMonarchIndex !== previousMonarchIndex && newMonarchIndex >= 0 && !hasMonarch) {
    actionText += ` Monarch: ${getPlayerLogLabel(newMonarchIndex)}.`;
  }

  addGameLogEntry({
    turn: turnNumber,
    activePlayerName,
    tone: getGameLogToneFromTypes(types),
    message: actionText
  });

  deathEvents.forEach(event => {
    if (!matchEliminations[event.targetIndex]?.cause) {
      matchEliminations[event.targetIndex] = {
        turn: turnNumber,
        cause: event.cause
      };
    }
    addGameLogEntry({
      turn: turnNumber,
      activePlayerName,
      tone: event.tone,
      message: `${getPlayerLogLabel(event.targetIndex)} died by ${event.cause}.`
    });
  });

  if (deathEvents.length > 0) {
    lastEliminationCause = getDominantDeathCause(deathEvents, types);
    lastEliminationSelections = getDefaultEndGameSelectionsFromCause(lastEliminationCause);
  }

  // -------------------------
  // Cleanup & Render
  // -------------------------
  damageSourceIndex = null;
  damageTargetIndex = null;

  saveState();
  render();

  requestAnimationFrame(() => {
    const useStaggeredShake = damageSelfMode === "All" || damageSelfMode === "Others";
    targetIndices.forEach((ti, orderIndex) => {
      animatePlayerStat(ti, "life", oldStates[ti].life, players[ti].life);
      animatePlayerStat(ti, "poison", oldStates[ti].poison, players[ti].poison);

      if (players[ti].life < oldStates[ti].life) {
        flashPlayer(ti, "damage-flash");
        shakePlayer(ti, {
          delayMs: useStaggeredShake ? (orderIndex * 55) + ((ti % 3) * 18) : 0,
          variant: useStaggeredShake ? ((orderIndex + ti) % 3) : 0
        });
      }
      if (players[ti].life > oldStates[ti].life) flashPlayer(ti, "heal-flash");
      if (players[ti].poison > oldStates[ti].poison) flashPlayer(ti, "poison-flash");
    });

    if (has("Lifelink") && lifelinkHeal > 0) {
      animatePlayerStat(sourceIndex, "life", oldStates[sourceIndex].life, players[sourceIndex].life);
      flashPlayer(sourceIndex, "heal-flash");
    }
  });

  checkGameEnd();
  closeDamageMode();
  autoPassIfActivePlayerDead();
  cleanupDamageArrow();
  triggerHaptic("success");
}

function cancelDamage() {
  damageSourceIndex = null;
  damageTargetIndex = null;
  pauseBtn.classList.remove("hidden");
  closeDamageMode();
  triggerHaptic("tap");
}


function setDamageTargetOption(option) {
  damageSelfMode = option;
  updateDamageButtonUI();
  
  // Visual toggle
  const allBtn = document.getElementById("damage-all-btn");
  const othersBtn = document.getElementById("damage-others-btn");

  allBtn.classList.toggle("active", option === "all");
  othersBtn.classList.toggle("active", option === "others");
}



//////////////////////////////////
//      DAMAGE ANIMATION        //
//////////////////////////////////
function flashPlayer(index, type) {

  const el = document.getElementById("player" + index);
  if (!el) return;

  if (type === "heal-flash") {
    spawnHealParticles(el, 3);
  }
  if (type === "poison-flash") {
    spawnPoisonParticles(el, 2);
  }

  el.classList.remove("damage-flash","heal-flash","poison-flash");

  requestAnimationFrame(() => {
    el.classList.add(type);
  });

}

function shakePlayer(index, options = {}) {
  const el = document.getElementById("player" + index);
  if (!el) return;
  const delayMs = Math.max(0, Number(options.delayMs) || 0);
  const variant = Math.abs(Number(options.variant) || 0) % 3;
  const existingTimer = Number(el.dataset.shakeTimer || 0);
  const baseScale = el.classList.contains("active") ? 1.02 : 0.98;

  if (existingTimer) {
    clearTimeout(existingTimer);
    el.dataset.shakeTimer = "";
  }

  if (el._impactShakeAnimation) {
    el._impactShakeAnimation.cancel();
    el._impactShakeAnimation = null;
  }

  const shakeFramesByVariant = [
    [
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.45vmin, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.55vmin, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.4vmin, 0.18vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.38vmin, -0.18vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.18vmin, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` }
    ],
    [
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.4vmin, -0.12vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.52vmin, 0.12vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.34vmin, 0.24vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.28vmin, -0.22vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.14vmin, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` }
    ],
    [
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.3vmin, -0.2vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.48vmin, 0.16vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.42vmin, 0, 0)` },
      { transform: `scale(${baseScale}) translate3d(0.24vmin, -0.18vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(-0.12vmin, 0.12vmin, 0)` },
      { transform: `scale(${baseScale}) translate3d(0, 0, 0)` }
    ]
  ];

  const startShake = () => {
    el.dataset.shakeTimer = "";
    el._impactShakeAnimation = el.animate(shakeFramesByVariant[variant], {
      duration: 580,
      easing: "ease-in-out"
    });
    el._impactShakeAnimation.addEventListener("finish", () => {
      el._impactShakeAnimation = null;
      el.style.transform = "";
    }, { once: true });
  };

  if (delayMs > 0) {
    const timerId = window.setTimeout(() => {
      startShake();
    }, delayMs);
    el.dataset.shakeTimer = String(timerId);
  } else {
    startShake();
  }
}

function spawnHealParticles(playerEl, count = 3) {
  if (!playerEl) return;

  const rect = playerEl.getBoundingClientRect();
  const maxStartRadius = Math.max(10, Math.min(rect.width, rect.height) * 0.25);

  for (let i = 0; i < count; i++) {
    const p = document.createElement("span");
    p.className = "heal-particle";
    p.textContent = "+";

    const startX = (Math.random() * 2 - 1) * maxStartRadius;
    const startY = (Math.random() * 2 - 1) * maxStartRadius;
    const driftX = (Math.random() * 2 - 1) * 26;
    const delay = i * 120;
    const duration = 1040 + Math.random() * 320;

    p.style.setProperty("--p-start-x", `${startX.toFixed(1)}px`);
    p.style.setProperty("--p-start-y", `${startY.toFixed(1)}px`);
    p.style.setProperty("--p-drift-x", `${driftX.toFixed(1)}px`);
    p.style.animationDelay = `${delay}ms`;
    p.style.animationDuration = `${duration.toFixed(0)}ms`;

    p.addEventListener("animationend", () => p.remove(), { once: true });
    playerEl.appendChild(p);
  }
}

function spawnPoisonParticles(playerEl, count = 2) {
  if (!playerEl) return;

  const rect = playerEl.getBoundingClientRect();
  const maxStartRadius = Math.max(10, Math.min(rect.width, rect.height) * 0.25);

  for (let i = 0; i < count; i++) {
    const p = document.createElement("span");
    p.className = "poison-particle";
    p.innerHTML = '<img src="./icons/Poison.svg" class="poison-particle-icon icon-img" alt="">';

    const startX = (Math.random() * 2 - 1) * maxStartRadius;
    const startY = (Math.random() * 2 - 1) * maxStartRadius;
    const driftX = (Math.random() * 2 - 1) * 22;
    const delay = i * 100;
    const duration = 1040 + Math.random() * 300;

    p.style.setProperty("--p-start-x", `${startX.toFixed(1)}px`);
    p.style.setProperty("--p-start-y", `${startY.toFixed(1)}px`);
    p.style.setProperty("--p-drift-x", `${driftX.toFixed(1)}px`);
    p.style.animationDelay = `${delay}ms`;
    p.style.animationDuration = `${duration.toFixed(0)}ms`;

    p.addEventListener("animationend", () => p.remove(), { once: true });
    playerEl.appendChild(p);
  }
}

function animateValue(el, start, end) {

  const duration = 950;
  const range = end - start;
  const startTime = performance.now();

  function update(now) {

    const progress = Math.min((now - startTime) / duration, 1);
    const value = Math.round(start + range * progress);

    if (el.classList.contains("poison")) {
      el.textContent = value;
    } else {
      el.childNodes[0].nodeValue = value;
    }

    if (progress < 1) requestAnimationFrame(update);
  }

  requestAnimationFrame(update);
}

function animatePlayerStat(index, stat, oldValue, newValue) {

  const player = document.querySelector(`#player${index}`);
  if (!player) return;

  const bg = player.querySelector(".bg");
  const lifeEl = player.querySelector(".life");

  if (!bg || !lifeEl) return;

  // LIFE ANIMATION
  if (stat === "life") {

    animateValue(lifeEl, oldValue, newValue);

    let flashClass = null;

    if (newValue < oldValue) flashClass = "damage-flash";
    if (newValue > oldValue) flashClass = "heal-flash";

    if (flashClass) {
      bg.classList.add(flashClass);

      bg.addEventListener("animationend", () => {
        bg.classList.remove(flashClass);
      }, { once: true });
    }

  }

  // POISON ANIMATION
  if (stat === "poison") {

  const poisonCorner = player.querySelector(".poison-corner");
  if (!poisonCorner) return;

  let poisonEl = poisonCorner.querySelector(".poison");

  // If poison span does not exist yet, create it
  if (!poisonEl) {
    poisonEl = document.createElement("span");
    poisonEl.className = "poison";
    poisonEl.textContent = "0";
    poisonCorner.appendChild(poisonEl);
  }

  poisonCorner.classList.toggle("is-empty", newValue <= 0);
  animateValue(poisonEl, oldValue, newValue);

  bg.classList.add("poison-flash");

  bg.addEventListener("animationend", () => {
    bg.classList.remove("poison-flash");
  }, { once: true });

}

}



//////////////////////////////////
//             ENDGAME          //
//////////////////////////////////
function createResetButton() {
  const startScreen = document.getElementById("start-screen");
  const playerButtons = document.getElementById("player-buttons");
  if (playerButtons) playerButtons.classList.add("hidden");

  let pauseActions = document.getElementById("pause-actions");
  if (!pauseActions) {
    pauseActions = document.createElement("div");
    pauseActions.id = "pause-actions";
    pauseActions.classList.add("hidden");
    startScreen.appendChild(pauseActions);
  }

  let endGameBtn = document.getElementById("end-game-btn");
  if (!endGameBtn) {
    endGameBtn = document.createElement("button");
    endGameBtn.id = "end-game-btn";
    endGameBtn.textContent = "End Game";
    endGameBtn.addEventListener("click", endGameFromPause);
    pauseActions.appendChild(endGameBtn);
  } else if (endGameBtn.parentElement !== pauseActions) {
    pauseActions.appendChild(endGameBtn);
  }

  const undoBtn = document.getElementById("undo-btn");
  if (undoBtn && !undoBtn.dataset.bound) {
    undoBtn.addEventListener("click", undoLastMove);
    undoBtn.dataset.bound = "1";
  }

  const gameLogBtn = document.getElementById("gamelog-btn");
  if (gameLogBtn && !gameLogBtn.dataset.bound) {
    gameLogBtn.addEventListener("click", toggleGameLogPanel);
    gameLogBtn.dataset.bound = "1";
  }

  ensureGameLogPanel();
  renderGameLogPanel();

  updateUndoButtonState();
}

function setPauseMenuControlsVisible(visible) {
  const shouldShow = visible && !isGameOver;
  const undoBtn = document.getElementById("undo-btn");
  const gameLogBtn = document.getElementById("gamelog-btn");
  const pauseActions = document.getElementById("pause-actions");

  if (undoBtn) undoBtn.classList.toggle("hidden", !shouldShow);
  if (gameLogBtn) gameLogBtn.classList.toggle("hidden", !shouldShow);
  if (pauseActions) pauseActions.classList.toggle("hidden", !shouldShow);
}

function ensureGameLogPanel() {
  const startScreen = document.getElementById("start-screen");
  if (!startScreen) return null;

  let panel = document.getElementById("game-log-panel");
  if (!panel) {
    panel = document.createElement("div");
    panel.id = "game-log-panel";
    panel.className = "hidden";
    panel.innerHTML = `
      <div class="game-log-header">
        <h3>Game Log</h3>
      </div>
      <div id="game-log-list" class="game-log-list"></div>
    `;
    startScreen.appendChild(panel);
  }

  return panel;
}

function renderGameLogPanel() {
  const panel = ensureGameLogPanel();
  if (!panel) return;

  const list = panel.querySelector("#game-log-list");
  if (!list) return;
  renderGameLogIntoList(list);
  bindDragScroll(list);
}

function closeGameLogPanel() {
  const panel = document.getElementById("game-log-panel");
  if (!panel) return;
  panel.classList.add("hidden");
}

function toggleGameLogPanel() {
  const panel = ensureGameLogPanel();
  if (!panel) return;
  renderGameLogPanel();
  panel.classList.toggle("hidden");
}

function renderGameLogIntoList(listEl) {
  if (!listEl) return;

  if (!gameLog.length) {
    listEl.innerHTML = `<div class="game-log-empty">No actions yet.</div>`;
    return;
  }

  listEl.innerHTML = gameLog
    .map(entry => `
      <div class="game-log-entry">
        <div class="game-log-meta">
          <span class="game-log-turn">${isDuelMode() ? `Game ${entry.game || 1} - ` : ""}Turn ${entry.turn}</span>
          <span class="game-log-sep"> - </span>
          <span class="game-log-player">${entry.activePlayerName || "Unknown Player"}</span>
        </div>
        <div class="game-log-text game-log-text-${entry.tone || "default"}">${escapeHtml(getDisplayLabel(entry.message || ""))}</div>
      </div>
    `)
    .join("");
}

function normalizeEndGameSelections(selections) {
  const set = new Set(
    (Array.isArray(selections) ? selections : [])
      .filter(cause => ENDGAME_PRIMARY_CAUSES.includes(cause))
  );

  // Combat and non-combat are mutually exclusive primary paths.
  if (set.has("Combat Damage") && set.has("Non-Combat Damage")) {
    set.delete("Non-Combat Damage");
  }

  // Commander requires Combat Damage.
  if (set.has("Commander")) set.add("Combat Damage");
  if (!set.has("Combat Damage")) set.delete("Commander");

  // Poison/Combo/Wincon/Milled require Non-Combat Damage.
  const nonCombatDependents = ["Poison", "Combo", "Wincon", "Milled"];
  if (nonCombatDependents.some(cause => set.has(cause))) {
    set.add("Non-Combat Damage");
  }
  if (!set.has("Non-Combat Damage")) {
    nonCombatDependents.forEach(cause => set.delete(cause));
  }

  return Array.from(set);
}

function getDefaultEndGameSelectionsFromCause(cause) {
  if (cause === "Commander") return normalizeEndGameSelections(["Combat Damage", "Commander"]);
  if (cause === "Poison") return normalizeEndGameSelections(["Non-Combat Damage", "Poison"]);
  if (cause === "Wincon") return normalizeEndGameSelections(["Non-Combat Damage", "Wincon"]);
  if (cause === "Milled") return normalizeEndGameSelections(["Non-Combat Damage", "Milled"]);
  if (cause === "Non-Combat Damage") return normalizeEndGameSelections(["Non-Combat Damage"]);
  if (cause === "Combat Damage") return normalizeEndGameSelections(["Combat Damage"]);
  return [];
}

function canAllowEmptyEndGameSelection() {
  return winnerIndex === null || winnerIndex === undefined || winnerIndex < 0;
}

function getDisabledEndGameCauses(selections = endGameSelectedCauses) {
  const selectedSet = new Set(normalizeEndGameSelections(selections));
  const disabled = new Set();

  if (selectedSet.has("Combat Damage")) {
    disabled.add("Non-Combat Damage");
    ["Poison", "Combo", "Wincon", "Milled"].forEach(cause => disabled.add(cause));
  }

  if (selectedSet.has("Non-Combat Damage")) {
    disabled.add("Combat Damage");
    disabled.add("Commander");
  }

  return disabled;
}

function ensureValidEndGameCause({ allowEmpty = canAllowEmptyEndGameSelection() } = {}) {
  const fallbackSelections = getDefaultEndGameSelectionsFromCause(lastEliminationCause);
  const requiredFallback = fallbackSelections.length > 0
    ? fallbackSelections
    : normalizeEndGameSelections(["Combat Damage"]);

  if (!Array.isArray(endGameSelectedCauses) || endGameSelectedCauses.length === 0) {
    endGameSelectedCauses = allowEmpty ? [] : requiredFallback;
    return;
  }

  endGameSelectedCauses = normalizeEndGameSelections(endGameSelectedCauses);
  if (isDuelMode()) {
    endGameSelectedCauses = endGameSelectedCauses.filter(cause => cause !== "Commander");
  }
  if (!allowEmpty && endGameSelectedCauses.length === 0) {
    endGameSelectedCauses = requiredFallback;
  }
}

function updateEndCauseButtonUI() {
  const endCauseButtons = document.getElementById("end-cause-buttons");
  if (!endCauseButtons) return;
  const selectedSet = new Set(endGameSelectedCauses);
  const disabledSet = getDisabledEndGameCauses(endGameSelectedCauses);

  endCauseButtons.querySelectorAll("button").forEach((btn) => {
    const cause = btn.dataset.cause;
    const shouldHide = isDuelMode() && cause === "Commander";
    btn.classList.toggle("hidden", shouldHide);
    btn.classList.toggle("active", selectedSet.has(cause));
    btn.disabled = shouldHide || (disabledSet.has(cause) && !selectedSet.has(cause));
  });
}

function renderEndDuelSummary(currentWinnerIndex) {
  const summaryEl = document.getElementById("end-duel-summary");
  if (!summaryEl) return;

  summaryEl.classList.add("hidden");
  summaryEl.innerHTML = "";

  if (!isDuelMode()) return;

  const projected = getProjectedDuelSeriesState(currentWinnerIndex);
  const seriesComplete = isDuelSeriesCompleteForState(projected);
  if (!seriesComplete) return;

  const wins0 = projected.wins?.[0] || 0;
  const wins1 = projected.wins?.[1] || 0;
  const seriesWinnerIndex = getDuelSeriesWinnerIndex(projected);
  const p1ActiveClass = seriesWinnerIndex === 0 ? "winner" : "";
  const p2ActiveClass = seriesWinnerIndex === 1 ? "winner" : "";

  summaryEl.innerHTML = `
    <div class="duel-summary-label">Round Results</div>
    <div class="duel-summary-scoreline">
      <span class="duel-summary-score ${p1ActiveClass}">${wins0}</span>
      <span class="duel-summary-sep">-</span>
      <span class="duel-summary-score ${p2ActiveClass}">${wins1}</span>
    </div>
  `;
  summaryEl.classList.remove("hidden");
}

function clearSeriesWinnerSeatHighlight() {
  document.querySelectorAll(".player.series-winner-highlight").forEach((el) => {
    el.classList.remove("series-winner-highlight");
  });
}

function applySeriesWinnerSeatHighlight(playerIndex) {
  clearSeriesWinnerSeatHighlight();
  if (!Number.isInteger(playerIndex) || playerIndex < 0) return;
  const winnerEl = document.getElementById(`player${playerIndex}`);
  winnerEl?.classList.add("series-winner-highlight");
}

function updateEndScreenActions() {
  const primaryBtn = document.getElementById("new-game-btn");
  const menuBtn = document.getElementById("back-menu-btn");
  if (!primaryBtn || !menuBtn) return;

  if (isDuelMode()) {
    const isSeriesCompleteAfterCurrentGame = isCurrentDuelGameFinal();
    primaryBtn.textContent = "Next Game";
    primaryBtn.classList.toggle("hidden", isSeriesCompleteAfterCurrentGame);
    menuBtn.textContent = "Back to Menu";
    menuBtn.classList.toggle("hidden", !isSeriesCompleteAfterCurrentGame);
    return;
  }

  primaryBtn.textContent = "New Game";
  primaryBtn.classList.remove("hidden");
  menuBtn.textContent = "Back to Menu";
  menuBtn.classList.remove("hidden");
}

function getEndCauseTone(causeLabel) {
  if (causeLabel.includes("Poison")) return "poison";
  if (causeLabel.includes("Commander") || causeLabel.includes("Combat") || causeLabel.includes("Non-Combat")) return "damage";
  return "default";
}

function setupEndCauseButtons() {
  const endCauseButtons = document.getElementById("end-cause-buttons");
  if (!endCauseButtons || endCauseButtons.dataset.bound === "1") return;

  endCauseButtons.addEventListener("click", (event) => {
    const btn = event.target.closest("button[data-cause]");
    if (!btn) return;

    const cause = btn.dataset.cause;
    if (btn.disabled) return;
    const set = new Set(endGameSelectedCauses);
    if (set.has(cause)) {
      set.delete(cause);
    } else {
      set.add(cause);
    }

    endGameSelectedCauses = normalizeEndGameSelections(Array.from(set));
    ensureValidEndGameCause();
    updateEndCauseButtonUI();
    saveState();
  });

  endCauseButtons.dataset.bound = "1";
}

function renderEndGameLogPanel() {
  const list = document.getElementById("end-log-list");
  if (!list) return;
  renderGameLogIntoList(list);
  bindDragScroll(list);
}

function finalizeEndGameSelection(actionType) {
  ensureValidEndGameCause({ allowEmpty: canAllowEmptyEndGameSelection() });
  syncActivePlayerTimer();

  const winnerName = winnerIndex !== null && winnerIndex >= 0
    ? getPlayerNameForLog(players[winnerIndex], winnerIndex)
    : null;
  const orderedCauses = ENDGAME_PRIMARY_CAUSES.filter(cause => endGameSelectedCauses.includes(cause));
  const finalCauseLabel = orderedCauses.join(" + ");
  const causeSummary = finalCauseLabel || "Unspecified";
  const displayCauseSummary = getDisplayLabel(causeSummary);
  const message = winnerName
    ? `${winnerName} won by ${displayCauseSummary}.`
    : finalCauseLabel
      ? `Game ended with no winner (${displayCauseSummary}).`
      : "Game ended with no winner.";

  addGameLogEntry({
    turn: turnNumber,
    activePlayerName: winnerName || getPlayerNameForLog(players[activePlayerIndex], activePlayerIndex),
    tone: getEndCauseTone(causeSummary),
    message
  });

  // Persist the user's final end-screen reason edits before any transition action.
  lastEliminationSelections = [...orderedCauses];
  lastEliminationCause = finalCauseLabel || null;

  if (isDuelMode()) {
    duelSeries = getProjectedDuelSeriesState(winnerIndex);
  }

  archiveCompletedGame(finalCauseLabel, message);
  saveState();
  clearResumeSessions();
  triggerHaptic(actionType === "menu" ? "tap" : "success");

  if (actionType === "next") {
    startNextDuelGame();
  } else if (actionType === "menu") {
    backToMenuFromEnd();
  } else {
    openRematchSetupFromEnd();
  }
}

function buildDuelContinuationSeats() {
  return Array.from({ length: 6 }, (_, index) => ({
    ...getDefaultSeatState(index),
    profileName: (players[index]?.name || `Player ${index + 1}`).trim() || `Player ${index + 1}`
  }));
}

function startNextDuelGame() {
  if (!isDuelMode()) return;
  const nextSeries = normalizeDuelSeriesState({
    ...duelSeries,
    currentGame: getCompletedDuelGamesCount() + 1
  });
  pendingDuelContinuation = {
    nextSeries,
    gameLog: [...gameLog]
  };

  const state = ensureSetupState();
  state.step = "seats";
  state.mode = "magic";
  state.playerCount = 2;
  state.matchLength = nextSeries.matchLength;
  state.startingLife = starting_life;
  state.startingPlayerIndex = Math.min(1, Math.max(0, Number(state.startingPlayerIndex) || 0));
  state.showStarterPicker = false;
  state.forceDeckSelection = false;
  state.seats = buildDuelContinuationSeats();

  isGameOver = false;
  const gameEl = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");
  gameEl?.classList.remove("blurred");
  startScreen?.classList.remove("hidden");
  document.getElementById("end-screen")?.classList.add("hidden");
  renderStartSetupScreen();
}

function endGameFromPause() {
  winnerIndex = null;
  lastEliminationCause = null;
  lastEliminationSelections = [];
  saveState();
  openEndMenu(undefined);
}

function openRematchSetupFromEnd() {
  const rematchState = buildRematchSetupState();

  localStorage.removeItem(STORAGE_KEY);
  clearResumeSessions();

  hasStartedGame = false;
  selectedPlayerCount = 0;
  gameMode = rematchState.mode;
  resetDuelSeriesState(rematchState.matchLength);
  starting_life = rematchState.startingLife;
  isGameOver = false;
  isPaused = true;
  winnerIndex = null;
  undoStack = [];
  turnNumber = 1;
  gameLog = [];
  lastEliminationCause = null;
  lastEliminationSelections = [];
  endGameSelectedCauses = [];
  resetMatchStats();

  players.forEach((p, index) => {
    const seat = rematchState.seats[index] || getDefaultSeatState(index);
    p.life = rematchState.startingLife;
    p.name = (seat.profileName || "").trim() || `Player ${index + 1}`;
    p.commander = "";
    p.commanderArtId = "";
    p.image = getDefaultPlayerBackground(index, rematchState.mode);
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  });

  if (turnInterval) clearInterval(turnInterval);
  turnInterval = null;
  turnStartTime = null;
  pauseStartedAt = null;

  const gameScreen = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");
  const endScreen = document.getElementById("end-screen");
  const playerButtons = document.getElementById("player-buttons");

  endScreen.classList.add("hidden");
  gameScreen.classList.remove("blurred");
  startScreen.classList.remove("hidden");
  startScreen.classList.add("setup-open");
  playerButtons?.classList.remove("hidden");

  setupState = rematchState;
  setupStartScreen();
  renderStartSetupScreen();

  setPauseMenuControlsVisible(false);
  closeGameLogPanel();
  pauseBtn.classList.add("hidden");
  pauseBtn.classList.remove("active");
  setPauseButtonIcon(false);

  updateUndoButtonState();
}

function backToMenuFromEnd() {
  localStorage.removeItem(STORAGE_KEY);
  clearResumeSessions();

  hasStartedGame = false;
  selectedPlayerCount = 0;
  gameMode = "commander";
  resetDuelSeriesState();
  starting_life = 40;
  isGameOver = false;
  isPaused = true;
  winnerIndex = null;
  undoStack = [];
  turnNumber = 1;
  gameLog = [];
  lastEliminationCause = null;
  lastEliminationSelections = [];
  endGameSelectedCauses = [];
  resetMatchStats();

  players.forEach(p => {
    p.life = starting_life;
    p.commanderArtId = "";
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  });

  if (turnInterval) clearInterval(turnInterval);
  turnInterval = null;
  turnStartTime = null;
  pauseStartedAt = null;

  const gameScreen = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");
  const endScreen = document.getElementById("end-screen");
  const playerButtons = document.getElementById("player-buttons");

  render();
  gameScreen.classList.remove("blurred");
  endScreen.classList.add("hidden");
  startScreen.classList.remove("hidden");
  resetSetupState();
  setupStartScreen();
  startScreen.classList.add("setup-open");
  playerButtons?.classList.remove("hidden");
  renderStartSetupScreen();

  setPauseMenuControlsVisible(false);
  closeGameLogPanel();
  pauseBtn.classList.add("hidden");
  pauseBtn.classList.remove("active");
  setPauseButtonIcon(false);

  updateUndoButtonState();
}

/* =========================
   Game Flow: Reset / End
   ========================= */
function resetGame() {
  localStorage.removeItem(STORAGE_KEY);
  clearResumeSessions();
  isGameOver = false;
  undoStack = [];
  turnNumber = 1;
  gameLog = [];
  lastEliminationCause = null;
  lastEliminationSelections = [];
  endGameSelectedCauses = [];
  resetMatchStats();

  // Reset player data only
  players.forEach(p => {
    p.life = starting_life;
    p.commanderArtId = "";
    p.turnTime = 0;
    p.totalTime = 0;
    p.poison = 0;
    p.commanderDamage = {};
    p.monarch = false;
  });

  // Reset turn system
  activePlayerIndex = 0;

  // Stop timer and restart cleanly
  if (turnInterval) clearInterval(turnInterval);
  turnInterval = null;
  turnStartTime = null;

  // Close pause mode
  isPaused = false;

  const gameScreen = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");

  gameScreen.classList.remove("blurred");
  startScreen.classList.add("hidden");
  document.getElementById("end-screen").classList.add("hidden");
  document.getElementById("player-buttons")?.classList.add("hidden");
  setPauseButtonIcon(false);
  setPauseMenuControlsVisible(false);
  closeGameLogPanel();

  // Re-render with SAME layout
  render();
  startTurnTimer(true);
  updateUndoButtonState();
}


function getAlivePlayers() {
  return players
    .map((p, index) => ({ p, index }))
    .filter(obj => obj.p.life > 0);
}

function openEndMenu(winnerIndex) {

  isGameOver = true;
  isPaused = true;
  const hasWinner = winnerIndex !== undefined && winnerIndex !== null && winnerIndex >= 0;
  const projectedSeries = isDuelMode() ? getProjectedDuelSeriesState(winnerIndex) : null;
  const isFinalDuelScreen = isDuelMode() && isDuelSeriesCompleteForState(projectedSeries);
  const seriesWinnerIndex = isFinalDuelScreen ? getDuelSeriesWinnerIndex(projectedSeries) : null;

  // In duel, keep the game winner visually active on the board.
  if (isDuelMode() && hasWinner) {
    activePlayerIndex = winnerIndex;
    render();
  }

  applySeriesWinnerSeatHighlight(isFinalDuelScreen ? seriesWinnerIndex : null);

  // Show end screen
  const endScreen = document.getElementById("end-screen");
  endScreen.classList.toggle("no-winner", !hasWinner);
  endScreen.classList.remove("hidden");

  document.getElementById("game").classList.add("blurred");

  // Hide pause button
  pauseBtn.classList.add("hidden");

  // Hide pause menu
  document.getElementById("start-screen").classList.add("hidden");
  document.getElementById("player-buttons")?.classList.add("hidden");
  setPauseMenuControlsVisible(false);
  closeGameLogPanel();

  document.getElementById("winner-text").textContent =
    hasWinner
      ? players[winnerIndex].name
      : "No Winner";

  const endBg = document.getElementById("end-screen-bg");
  if (endBg) {
    if (isDuelMode() || isFinalDuelScreen) {
      endBg.style.backgroundImage = "none";
    } else {
      const bgPlayerIndex = Number.isInteger(seriesWinnerIndex)
        ? seriesWinnerIndex
        : (hasWinner ? winnerIndex : null);
      if (Number.isInteger(bgPlayerIndex) && players[bgPlayerIndex]) {
        endBg.style.backgroundImage = `
          linear-gradient(180deg, rgba(0,0,0,0.42) 0%, rgba(0,0,0,0.68) 100%),
          url("${players[bgPlayerIndex].image}")
        `;
      } else {
        endBg.style.backgroundImage = "none";
      }
    }
  }

  // Always seed endgame causes from latest elimination outcome to avoid stale selections.
  endGameSelectedCauses = (Array.isArray(lastEliminationSelections) && lastEliminationSelections.length > 0)
    ? [...lastEliminationSelections]
    : getDefaultEndGameSelectionsFromCause(lastEliminationCause);

  ensureValidEndGameCause({ allowEmpty: !hasWinner });
  setupEndCauseButtons();
  updateEndCauseButtonUI();
  renderEndDuelSummary(winnerIndex);
  updateEndScreenActions();
  renderEndGameLogPanel();
  updateUndoButtonState();
  triggerHaptic("alert");
}


function checkGameEnd() {
  if (isGameOver) return true;

  const alive = players
    .slice(0, selectedPlayerCount)
    .filter(p => p.life > 0);

  if (alive.length <= 1) {
  isGameOver = true;

  const aliveWinnerIndex = players.slice(0, selectedPlayerCount).findIndex(p => p.life > 0);
  winnerIndex = aliveWinnerIndex >= 0 ? aliveWinnerIndex : null;

    saveState();

    openEndMenu(winnerIndex !== null ? winnerIndex : undefined);

    return true;
  }

  return false;
}

function applyLoadedUiState() {
  exitSetupGridPreview();
  const gameScreen = document.getElementById("game");
  const startScreen = document.getElementById("start-screen");

  if (!selectedPlayerCount) {
    hasStartedGame = false;
    pauseBtn.classList.add("hidden");
    startScreen.classList.remove("hidden");
    resetSetupState();
    setupStartScreen();
    return;
  }

  if (isGameOver) {
    openEndMenu(winnerIndex !== null && winnerIndex >= 0 ? winnerIndex : undefined);
    return;
  }

  pauseBtn.classList.remove("hidden");

  if (isPaused) {
    createResetButton();
    gameScreen.classList.add("blurred");
    startScreen.classList.remove("setup-open");
    startScreen.classList.remove("hidden");
    setPauseMenuControlsVisible(true);
    pauseBtn.classList.add("active");
    setPauseButtonIcon(true);
    // Start counting paused duration from refresh moment.
    pauseStartedAt = Date.now();
  } else {
    gameScreen.classList.remove("blurred");
    startScreen.classList.remove("setup-open");
    startScreen.classList.add("hidden");
    setPauseMenuControlsVisible(false);
    pauseBtn.classList.remove("active");
    setPauseButtonIcon(false);
    pauseStartedAt = null;
    closeGameLogPanel();
  }
}

function updateOrientationLock() {
  document.body.classList.toggle("portrait-locked-landscape", window.innerWidth > window.innerHeight);
}

/* =========================
   App Bootstrapping
   ========================= */
profileLibrary = loadProfileLibrary();
deckLibrary = loadDeckLibrary();
matchHistory = loadMatchHistory();
resumeSessions = loadResumeSessions();
startMenuBackdrop = loadStartMenuBackdrop();
void hydrateMissingDeckImages({ limit: 50 });

if ("serviceWorker" in navigator) {
  ensureServiceWorkerReady().then(() => {
    warmCommanderImageCache();
  });
  navigator.serviceWorker.addEventListener("controllerchange", () => {
    warmCommanderImageCache();
  });
}

window.addEventListener("online", () => {
  void hydrateMissingDeckImages({ limit: 50 });
});

const hasLoadedState = loadState();
if (!hasLoadedState) {
  hasStartedGame = false;
  selectedPlayerCount = 0;
  isPaused = true;
  resetSetupState();
}



/* =========================
   Damage Arrow Visualization
   ========================= */
function drawDamageArrow(sourceIndex, mouseX, mouseY) {

  const svg = document.getElementById("damage-arrow-layer");
  if (!svg) return;
  const arrowColor = getPlayerArrowColor(sourceIndex);

  const gameRect = game.getBoundingClientRect();

  const startX = dragStartX - gameRect.left;
  const startY = dragStartY - gameRect.top;

  const endX = mouseX - gameRect.left;
  const endY = mouseY - gameRect.top;

  const distance = Math.hypot(endX - startX, endY - startY);
  const curve = Math.min(distance * 0.35, 200);

  const controlX = (startX + endX) / 2;
  const controlY = (startY + endY) / 2 - curve;

  const path = document.createElementNS("http://www.w3.org/2000/svg", "path");

  path.setAttribute(
    "d",
    `M ${startX} ${startY} Q ${controlX} ${controlY} ${endX} ${endY}`
  );

  path.classList.add("damage-arrow");
  path.style.stroke = arrowColor;
  path.style.filter = `drop-shadow(0 0 6px ${arrowColor})`;

  svg.appendChild(path);

  drawArrowHead(svg, controlX, controlY, endX, endY, arrowColor, sourceIndex);
}

function drawArrowHead(svg, cx, cy, ex, ey, arrowColor = "#f55831", sourceIndex = null) {

  const angle = Math.atan2(ey - cy, ex - cx);
  const isJudyArrow = Number.isInteger(sourceIndex) && isJudyPlayerName(players[sourceIndex]?.name);
  const size = 18;
  const offset = 10;

  const tipX = ex + Math.cos(angle) * offset;
  const tipY = ey + Math.sin(angle) * offset;

  if (isJudyArrow) {
    const judyForwardBias = 30;
    const judyTipX = tipX + Math.cos(angle) * judyForwardBias;
    const judyTipY = tipY + Math.sin(angle) * judyForwardBias;
    const markerWidth = size * 2.35;
    const markerHeight = size * 1.2;
    const markerGroup = document.createElementNS("http://www.w3.org/2000/svg", "g");
    markerGroup.classList.add("damage-arrow-head-wrap");
    markerGroup.setAttribute("transform", `translate(${judyTipX}, ${judyTipY}) rotate(${angle * 180 / Math.PI})`);

    const markerImage = document.createElementNS("http://www.w3.org/2000/svg", "image");
    markerImage.setAttribute("href", "./icons/JudyArrowHead.png");
    markerImage.setAttribute("x", String(-markerWidth));
    markerImage.setAttribute("y", String(-markerHeight / 2));
    markerImage.setAttribute("width", String(markerWidth));
    markerImage.setAttribute("height", String(markerHeight));
    markerImage.setAttribute("preserveAspectRatio", "xMidYMid meet");
    markerImage.style.filter = `drop-shadow(0 0 6px ${arrowColor})`;
    markerGroup.appendChild(markerImage);
    svg.appendChild(markerGroup);
    return;
  }

  const x2 = tipX - size * Math.cos(angle - Math.PI / 6);
  const y2 = tipY - size * Math.sin(angle - Math.PI / 6);

  const x3 = tipX - size * Math.cos(angle + Math.PI / 6);
  const y3 = tipY - size * Math.sin(angle + Math.PI / 6);

  const head = document.createElementNS("http://www.w3.org/2000/svg", "polygon");

  head.setAttribute(
    "points",
    `${tipX},${tipY} ${x2},${y2} ${x3},${y3}`
  );

  head.classList.add("damage-arrow-head");
  head.style.fill = arrowColor;
  head.style.filter = `drop-shadow(0 0 6px ${arrowColor})`;

  svg.appendChild(head);
}

function cleanupDamageArrow() {

  const svg = document.getElementById("damage-arrow-layer");
  if (!svg) return;

  svg.querySelectorAll(".damage-arrow, .damage-arrow-head, .damage-arrow-head-wrap")
     .forEach(el => el.remove());
}

function initExitConfirmGuard() {
  if (exitConfirmGuardInitialized) return;
  if (!window.history || typeof window.history.pushState !== "function") return;
  exitConfirmGuardInitialized = true;

  // Add one synthetic history entry so system back can be intercepted once.
  window.history.pushState({ lifexExitGuard: true }, "", window.location.href);

  window.addEventListener("popstate", () => {
    if (allowExitAfterConfirm) return;

    const shouldExit = window.confirm("Leave LifeX?");
    if (shouldExit) {
      allowExitAfterConfirm = true;
      window.history.back();
      return;
    }

    // Re-arm guard if user cancels.
    window.history.pushState({ lifexExitGuard: true }, "", window.location.href);
  });
}



/* =========================
   Global Event Wiring
   ========================= */
document.getElementById("pause-btn").addEventListener("click", togglePause);
document.getElementById("game").addEventListener("click", openStartMenuWhenNoGame);
document.getElementById("new-game-btn")?.addEventListener("click", () => {
  if (isDuelMode()) {
    finalizeEndGameSelection(isCurrentDuelGameFinal() ? "menu" : "next");
    return;
  }
  finalizeEndGameSelection("new");
});
document.getElementById("back-menu-btn")?.addEventListener("click", () => finalizeEndGameSelection("menu"));
document.getElementById("end-undo-btn")?.addEventListener("click", undoLastMoveFromEndScreen);
window.addEventListener("resize", updateGridLayout);
window.addEventListener("resize", () => updateScrollableFadeState(document));
window.addEventListener("resize", updateOrientationLock);
window.addEventListener("orientationchange", updateOrientationLock);
window.addEventListener("beforeunload", saveState);
window.addEventListener("pagehide", saveState);


window.addEventListener("contextmenu", (e) => e.preventDefault()); //PREVENT RIGHT CLICK

// Console helpers for quick troubleshooting:
// start2(), start3(), start4(), start5(), start6(), startPlayers(n)
/*window.startPlayers = (n) => quickStartGame(n);
window.start2 = () => quickStartGame(2);
window.start3 = () => quickStartGame(3);
window.start4 = () => quickStartGame(4);
window.start5 = () => quickStartGame(5);
window.start6 = () => quickStartGame(6);
*/


render();
setupStartScreen();
setupEndCauseButtons();
applyLoadedUiState();
initExitConfirmGuard();
setPauseButtonIcon(isPaused);
updateOrientationLock();

if (!isGameOver) {
  startTurnTimer();
}

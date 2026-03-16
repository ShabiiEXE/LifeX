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
let dragHoverTargetIndex = null;
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
const PERSISTENT_STATS_STORAGE_KEY = "lifeTrackerPersistentStatsV1";
const RESUME_SESSIONS_STORAGE_KEY = "lifeTrackerResumeSessionsV1";
const DEVICE_ID_STORAGE_KEY = "lifeXDeviceIdV1";
const CLOUD_SYNC_STORAGE_KEY = "lifeXCloudSyncV1";
const SYNC_TOMBSTONES_STORAGE_KEY = "lifeXSyncTombstonesV1";
const QR_TRANSFER_PREFIX = "LIFEX1:";
const SCRYFALL_SEARCH_TIMEOUT_MS = 3200;
const CLOUD_SYNC_PIN_LENGTH = 4;
const CLOUD_SYNC_POLL_MS = 15000;
const DEFAULT_PLAYER_BACKGROUND = "./img/default_back0.png";
const MENU_BACKGROUND = "./img/menu_back.png";
const DEFAULT_MAGIC_PLAYER_BACKGROUNDS = [
  "./img/default_back0.png",
  "./img/default_back1.png"
];
const CUSTOM_COMMANDER_ARTS = [
  { commanderName: "Bello, Bard of the Brambles", artRef: "/custom/bello1/", art: "./custom-art/custom_bello.png", setLabel: "Custom Art" },
  { commanderName: "Krenko, Mob Boss", artRef: "/custom/krenko1/", art: "./custom-art/custom_krenko.png", setLabel: "Custom Art" },
  { commanderName: "High Perfect Morcant", artRef: "/custom/morcant1/", art: "./custom-art/custom_morcant.png", setLabel: "Custom Art" },
  { commanderName: "Nekusar, the Mindrazer", artRef: "/custom/nekusar1/", art: "./custom-art/custom_nekuzar.png", setLabel: "Custom Art" },
  { commanderName: "Prosper, Tome-Bound", artRef: "/custom/prosper1/", art: "./custom-art/custom_prosper.png", setLabel: "Custom Art" },
  { commanderName: "Rith, the Awakener", artRef: "/custom/rith1/", art: "./custom-art/custom_rith.png", setLabel: "Custom Art" },
  { commanderName: "Pako, Arcane Retriever", artRef: "/custom/pako1/", art: "./custom-art/custom-pako.png", setLabel: "Custom Art" }
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
let persistentStats = null;
let resumeSessions = [];
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
let cloudSyncLoopId = null;
let cloudSyncInFlightPromise = null;
let cloudSyncPending = false;
let syncTombstones = null;

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

function isSingleSeatProfileEditorMode() {
  return setupGridPreviewActive && selectedPlayerCount === 1 && !hasStartedGame && !!setupState?.profileEditorMode;
}

function isProfileEditorMode(state = setupState) {
  return !!state?.profileEditorMode;
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
  const completedGames = Array.isArray(normalized.winners) ? normalized.winners.length : 0;
  const wins0 = normalized.wins?.[0] || 0;
  const wins1 = normalized.wins?.[1] || 0;

  if (completedGames >= normalized.matchLength) {
    if (wins0 > wins1) return 0;
    if (wins1 > wins0) return 1;
  }

  if (wins0 >= winsNeeded) return 0;
  if (wins1 >= winsNeeded) return 1;
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
  Delete: `<svg viewBox="0 0 2578.87 2513.38" class="icon-img" aria-hidden="true" focusable="false"><g fill="currentColor"><path d="M1990.23,2513.38H600.37c-54.12,0-106.71-10.63-156.28-31.6-47.81-20.22-90.72-49.15-127.54-85.96-36.82-36.82-65.74-79.73-85.96-127.54-20.97-49.58-31.6-102.16-31.6-156.28V812.72c0-77.32,62.68-140,140-140s140,62.68,140,140v1299.27c0,66.93,54.45,121.39,121.38,121.39h1389.86c66.93,0,121.39-54.46,121.39-121.39V812.72c0-77.32,62.68-140,140-140s140,62.68,140,140v1299.27c0,54.13-10.63,106.71-31.6,156.28-20.22,47.81-49.15,90.73-85.96,127.54-36.82,36.82-79.73,65.74-127.54,85.96-49.58,20.97-102.16,31.6-156.28,31.6Z"/><rect x="0" y="275.42" width="2578.87" height="279.38" rx="139.69" ry="139.69"/><rect x="1209.93" y="1372.7" width="1075.32" height="181.94" rx="90.97" ry="90.97" transform="translate(3211.26 -283.92) rotate(90)"/><rect x="757.65" y="1372.7" width="1075.32" height="181.94" rx="90.97" ry="90.97" transform="translate(2758.97 168.36) rotate(90)"/><rect x="309.28" y="1372.7" width="1075.32" height="181.94" rx="90.97" ry="90.97" transform="translate(2310.61 616.73) rotate(90)"/><path d="M1169.15,0h240.57c109.93,0,199.18,89.25,199.18,199.18v99.03h-638.93v-99.03c0-109.93,89.25-199.18,199.18-199.18Z"/></g></svg>`,
  GameLog: `<svg viewBox="0 0 2118.07 2721.76" class="icon-img" aria-hidden="true" focusable="false"><g fill="currentColor"><rect x=".97" y="1468.51" width="1193.66" height="218.02" rx="109.01" ry="109.01"/><rect x=".97" y="1930.88" width="1453.55" height="218.02" rx="109.01" ry="109.01"/><path d="M1978.07,2721.76H140c-77.32,0-140-62.68-140-140s62.68-140,140-140h1698.07v-1367.47c0-28.75-5.58-56.8-16.58-83.36-11-26.57-26.89-50.34-47.22-70.67l-576.45-576.45c-20.33-20.33-44.11-36.22-70.67-47.22-26.56-11-54.61-16.58-83.36-16.58H140C62.68,280,0,217.32,0,140S62.68,0,140,0h903.78c65.71,0,129.81,12.75,190.51,37.9,60.71,25.15,115.05,61.46,161.51,107.92l576.45,576.45c46.46,46.46,82.77,100.81,107.92,161.51s37.9,124.8,37.9,190.51v1507.47c0,77.32-62.68,140-140,140Z"/></g></svg>`,
  Monarch: `<svg viewBox="0 0 3003 1922.35" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M2490.04,1922.35H512.97c-64.29,0-120.32-43.79-135.85-106.18L4.16,318.06c-14.78-59.36,10.69-121.43,62.9-153.31,52.21-31.88,119.06-26.17,165.11,14.09l700.55,612.51L1382.53,66.2C1408.06,25.04,1453.06,0,1501.5,0s93.45,25.04,118.98,66.2l449.82,725.15,700.55-612.51c58.21-50.89,146.65-44.96,197.55,13.25,50.89,58.21,44.96,146.65-13.24,197.55l-824.72,721.08c-25.69,22.46-58.49,34.6-92.15,34.61-6.89,0-13.81-.51-20.73-1.54-40.65-6.08-76.58-29.73-98.25-64.66l-417.81-673.54-417.81,673.54c-21.67,34.93-57.59,58.57-98.25,64.66-40.65,6.08-81.93-6.01-112.87-33.06l-488.98-427.53,238.79,959.16h1867.65c77.32,0,140,62.68,140,140s-62.68,140-140,140Z"/></svg>`,
  Edit: `<svg viewBox="0 0 2040.37 2035.6" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1642.63,397.39c30.58,30.58,45.87,70.66,45.87,110.74,0,40.08-15.28,80.15-45.86,110.73L271.76,1989.73c-56,56-143.85,60.72-205.22,14.17-7.39-5.2-14.31-11.03-20.68-17.4-28.33-28.33-45.86-67.49-45.86-110.73v-744.09c0-86.49,70.11-156.6,156.6-156.6,43.25,0,82.4,17.53,110.74,45.87s45.86,67.49,45.86,110.73v373.66L1421.16,397.39c61.16-61.16,160.31-61.16,221.47,0Z"/><rect fill="currentColor" x="1727.49" y="0" width="312.88" height="312.88" rx="156.44" ry="156.44" transform="translate(441.17 1377.96) rotate(-45)"/></svg>`,
  Minus: `<svg viewBox="0 0 100 100" class="icon-img" aria-hidden="true" focusable="false"><rect x="12" y="39" width="60" height="18" rx="11" ry="11" fill="currentColor"/></svg>`,
  Ok: `<svg viewBox="0 0 2029.21 2029.21" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1014.6,0C454.25,0,0,454.25,0,1014.6s454.25,1014.61,1014.6,1014.61,1014.61-454.26,1014.61-1014.61S1574.95,0,1014.6,0ZM1014.6,1664.59c-358.97,0-649.98-291.01-649.98-649.99S655.63,364.62,1014.6,364.62s649.98,291.01,649.98,649.98-291,649.99-649.98,649.99Z"/></svg>`,
  Play: `<svg viewBox="0 0 1481.73 1698.19" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M1389.8,1011.15L285.67,1671.15C159.83,1746.38,0,1655.71,0,1509.1V189.09C0,42.48,159.83-48.19,285.67,27.04l1104.13,660c122.57,73.27,122.57,250.84,0,324.11Z"/></svg>`,
  Plus: `<svg viewBox="0 0 100 100" class="icon-img" aria-hidden="true" focusable="false"><rect x="16" y="42" width="68" height="16" rx="8" ry="8" fill="currentColor"/><rect x="42" y="16" width="16" height="68" rx="8" ry="8" fill="currentColor"/></svg>`,
  Profile: `<svg viewBox="0 0 1930.03 2421.39" class="icon-img" aria-hidden="true" focusable="false"><path fill="currentColor" d="M965.01,0C571.38,0,252.29,319.09,252.29,712.72s319.09,712.73,712.72,712.73,712.73-319.1,712.73-712.73S1358.63,0,965.01,0ZM965.01,1169.31c-252.16,0-456.59-204.42-456.59-456.59s204.42-456.59,456.59-456.59,456.59,204.42,456.59,456.59-204.42,456.59-456.59,456.59Z"/><path fill="currentColor" d="M1899.3,2096.72l-405.9-679.02c-62.57,53.9-133.47,98.4-210.5,131.3l369.71,622.36H277.41l370.51-622.02c-77.34-32.94-148.52-77.56-211.3-131.64L30.72,2096.72c-85.48,143.02,17.55,324.67,184.19,324.67h1500.21c166.63,0,269.68-181.65,184.18-324.67Z"/></svg>`,
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
  impact: [10, 86, 10, 86, 10, 86, 10, 86, 10, 86, 10, 90],
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

function normalizeCloudSyncPin(value) {
  const digitsOnly = `${value || ""}`.replace(/\D/g, "").slice(0, CLOUD_SYNC_PIN_LENGTH);
  return digitsOnly.length === CLOUD_SYNC_PIN_LENGTH ? digitsOnly : digitsOnly;
}

function normalizeCloudSyncPassword(value) {
  const digitsOnly = `${value || ""}`.replace(/\D/g, "").slice(0, CLOUD_SYNC_PIN_LENGTH);
  return digitsOnly.length === CLOUD_SYNC_PIN_LENGTH ? digitsOnly : digitsOnly;
}

function loadCloudSyncSession() {
  const parsed = safeJsonParse(localStorage.getItem(CLOUD_SYNC_STORAGE_KEY), {});
  const rooms = Array.isArray(parsed?.rooms)
    ? parsed.rooms
        .map((room, index) => {
          const pin = normalizeCloudSyncPin(room?.pin);
          const id = `${room?.id || `room-${index}`}`.trim() || `room-${index}`;
          const name = `${room?.name || ""}`.trim() || `Playgroup ${index + 1}`;
          const password = normalizeCloudSyncPassword(room?.password);
          if (pin.length !== CLOUD_SYNC_PIN_LENGTH) return null;
          return { id, name, pin, password };
        })
        .filter(Boolean)
    : [];
  const activeRoomId = `${parsed?.activeRoomId || ""}`.trim();
  return {
    rooms,
    activeRoomId: rooms.some(room => room.id === activeRoomId)
      ? activeRoomId
      : (rooms[0]?.id || "")
  };
}

function saveCloudSyncSession() {
  localStorage.setItem(CLOUD_SYNC_STORAGE_KEY, JSON.stringify({
    rooms: Array.isArray(cloudSyncSession?.rooms) ? cloudSyncSession.rooms : [],
    activeRoomId: `${cloudSyncSession?.activeRoomId || ""}`.trim()
  }));
}

function createEmptySyncTombstones() {
  return {
    profiles: [],
    decks: []
  };
}

function normalizeSyncTombstones(source) {
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

function loadSyncTombstones(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  return normalizeSyncTombstones(
    safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(SYNC_TOMBSTONES_STORAGE_KEY, roomId)), createEmptySyncTombstones())
  );
}

function saveSyncTombstones(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(SYNC_TOMBSTONES_STORAGE_KEY, roomId), JSON.stringify(normalizeSyncTombstones(syncTombstones)));
}

function mergeProfileTombstone(entries, profileName, deletedAt) {
  const normalizedProfileName = normalizeLibraryName(profileName);
  const nextEntries = Array.isArray(entries) ? entries : [];
  const existing = nextEntries.find((entry) => normalizeLibraryName(entry.profileName) === normalizedProfileName);
  if (existing) {
    existing.deletedAt = Math.max(existing.deletedAt || 0, deletedAt || 0);
    if (!existing.profileName) existing.profileName = `${profileName || ""}`.trim();
    return nextEntries;
  }
  nextEntries.push({
    profileName: `${profileName || ""}`.trim(),
    deletedAt
  });
  return nextEntries;
}

function mergeDeckTombstone(entries, ownerProfileName, commanderName, deletedAt) {
  const normalizedOwner = normalizeLibraryName(ownerProfileName);
  const normalizedCommander = normalizeLibraryName(commanderName);
  const nextEntries = Array.isArray(entries) ? entries : [];
  const existing = nextEntries.find((entry) =>
    normalizeLibraryName(entry.ownerProfileName) === normalizedOwner &&
    normalizeLibraryName(entry.commanderName) === normalizedCommander
  );
  if (existing) {
    existing.deletedAt = Math.max(existing.deletedAt || 0, deletedAt || 0);
    return nextEntries;
  }
  nextEntries.push({
    ownerProfileName: `${ownerProfileName || ""}`.trim(),
    commanderName: `${commanderName || ""}`.trim(),
    deletedAt
  });
  return nextEntries;
}

function recordProfileDeletionTombstone(profileName, deletedAt = Date.now()) {
  if (!profileName) return;
  syncTombstones.profiles = mergeProfileTombstone(syncTombstones.profiles, profileName, deletedAt);
  saveSyncTombstones();
}

function recordDeckDeletionTombstone(ownerProfileName, commanderName, deletedAt = Date.now()) {
  if (!ownerProfileName || !commanderName) return;
  syncTombstones.decks = mergeDeckTombstone(syncTombstones.decks, ownerProfileName, commanderName, deletedAt);
  saveSyncTombstones();
}

function getLatestProfileDeletion(profileName, tombstones = syncTombstones) {
  const normalizedProfileName = normalizeLibraryName(profileName);
  return (normalizeSyncTombstones(tombstones).profiles.find((entry) =>
    normalizeLibraryName(entry.profileName) === normalizedProfileName
  )?.deletedAt) || 0;
}

function getLatestDeckDeletion(ownerProfileName, commanderName, tombstones = syncTombstones) {
  const normalizedOwner = normalizeLibraryName(ownerProfileName);
  const normalizedCommander = normalizeLibraryName(commanderName);
  return (normalizeSyncTombstones(tombstones).decks.find((entry) =>
    normalizeLibraryName(entry.ownerProfileName) === normalizedOwner &&
    normalizeLibraryName(entry.commanderName) === normalizedCommander
  )?.deletedAt) || 0;
}

function mergeSyncTombstones(incomingTombstones) {
  const normalizedIncoming = normalizeSyncTombstones(incomingTombstones);
  normalizedIncoming.profiles.forEach((entry) => {
    syncTombstones.profiles = mergeProfileTombstone(syncTombstones.profiles, entry.profileName, entry.deletedAt);
  });
  normalizedIncoming.decks.forEach((entry) => {
    syncTombstones.decks = mergeDeckTombstone(syncTombstones.decks, entry.ownerProfileName, entry.commanderName, entry.deletedAt);
  });
  saveSyncTombstones();
}

function applySyncTombstonesToLocalData() {
  const profileDeletions = normalizeSyncTombstones(syncTombstones).profiles;
  const deckDeletions = normalizeSyncTombstones(syncTombstones).decks;

  const deletedProfileIds = new Set();
  profileLibrary = profileLibrary.filter((profile) => {
    const latestDeletion = getLatestProfileDeletion(profile?.name);
    const profileLastUsedAt = Number.isFinite(profile?.lastUsedAt) ? profile.lastUsedAt : 0;
    const shouldDelete = latestDeletion > 0 && latestDeletion >= profileLastUsedAt;
    if (shouldDelete && profile?.id) {
      deletedProfileIds.add(profile.id);
    }
    return !shouldDelete;
  });

  deckLibrary = deckLibrary.filter((deck) => {
    const ownerProfile = profileLibrary.find((profile) => profile.id === deck.ownerProfileId);
    const ownerProfileName = `${ownerProfile?.name || ""}`.trim();
    const commanderName = `${deck?.cardName || deck?.deckName || ""}`.trim();
    const latestProfileDeletion = ownerProfileName ? getLatestProfileDeletion(ownerProfileName) : 0;
    const latestDeckDeletion = ownerProfileName && commanderName ? getLatestDeckDeletion(ownerProfileName, commanderName) : 0;
    const deckLastUsedAt = Number.isFinite(deck?.lastUsedAt) ? deck.lastUsedAt : 0;
    return !(deletedProfileIds.has(deck.ownerProfileId) || latestProfileDeletion >= deckLastUsedAt || latestDeckDeletion >= deckLastUsedAt);
  });

  if (setupState?.seats) {
    setupState.seats.forEach((seat, index) => {
      const seatProfileName = `${seat?.profileName || ""}`.trim();
      const latestProfileDeletion = getLatestProfileDeletion(seatProfileName);
      if (seatProfileName && latestProfileDeletion > 0 && latestProfileDeletion >= 0 && !profileLibrary.find((profile) => profile.id === seat.profileId)) {
        const fallback = getDefaultSeatState(index);
        seat.profileId = "";
        seat.profileName = fallback.profileName;
        seat.isAddingProfile = false;
        seat.newProfileName = "";
        seat.isDeletingProfile = false;
        clearSeatDeckSelection(seat);
        return;
      }

      const ownerProfileName = seatProfileName;
      const commanderName = `${seat?.cardName || seat?.deckName || ""}`.trim();
      const latestDeckDeletion = ownerProfileName && commanderName ? getLatestDeckDeletion(ownerProfileName, commanderName) : 0;
      if (latestDeckDeletion > 0 && commanderName && !deckLibrary.find((deck) => deck.id === seat.deckId)) {
        clearSeatDeckSelection(seat, { preserveDeleteMode: !!seat?.isDeletingDeck });
      }
    });
  }

  saveProfileLibrary();
  saveDeckLibrary();
}

function refreshSetupStateForWorkspaceSwitch() {
  if (!setupState) return;
  setupState.seats = Array.from({ length: 6 }, (_, index) => getDefaultSeatState(index));
  setupState.syncRoomId = getActiveCloudSyncRoom()?.id || "";
  setupState.syncRoomName = getActiveCloudSyncRoom()?.name || "";
  setupState.syncPin = getActiveCloudSyncRoom()?.pin || "";
  setupState.syncPassword = getActiveCloudSyncRoom()?.password || "";
  setupState.syncConnected = !!getActiveCloudSyncRoom();
}

function loadWorkspaceSnapshot(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim(), { refreshSetup = true, shouldRender = true } = {}) {
  profileLibrary = loadProfileLibrary(roomId);
  deckLibrary = loadDeckLibrary(roomId);
  matchHistory = loadMatchHistory(roomId);
  persistentStats = loadPersistentStats(roomId);
  syncTombstones = loadSyncTombstones(roomId);
  applySyncTombstonesToLocalData();
  syncPersistentStatsFromHistory();
  resumeSessions = loadResumeSessions(roomId);
  void hydrateMissingDeckImages({ limit: 50 });
  if (refreshSetup && (!hasStartedGame || !selectedPlayerCount)) {
    refreshSetupStateForWorkspaceSwitch();
  }
  if (shouldRender && document.getElementById("start-screen")) {
    renderStartSetupScreen();
  }
}

function activateCloudSyncWorkspace(room, { shouldRender = true } = {}) {
  const currentRoomId = `${cloudSyncSession?.activeRoomId || ""}`.trim();
  const nextRoom = room ? upsertCloudSyncRoom(room, { setActive: true }) : null;
  const nextRoomId = `${nextRoom?.id || ""}`.trim();
  if (currentRoomId && currentRoomId !== nextRoomId) {
    persistWorkspaceSnapshot(currentRoomId);
  } else if (!currentRoomId && nextRoomId) {
    // First room connection adopts the current local workspace.
    persistWorkspaceSnapshot(nextRoomId);
    persistWorkspaceSnapshot("");
  }
  loadWorkspaceSnapshot(nextRoomId, { shouldRender });
  return nextRoom;
}

function clearActiveCloudSyncWorkspace({ shouldRender = true } = {}) {
  const currentRoomId = `${cloudSyncSession?.activeRoomId || ""}`.trim();
  if (currentRoomId) {
    persistWorkspaceSnapshot(currentRoomId);
  }
  loadWorkspaceSnapshot("", { shouldRender });
}

function getCloudSyncRooms() {
  return Array.isArray(cloudSyncSession?.rooms) ? cloudSyncSession.rooms : [];
}

function getActiveCloudSyncRoom() {
  const activeId = `${cloudSyncSession?.activeRoomId || ""}`.trim();
  return getCloudSyncRooms().find(room => room.id === activeId) || null;
}

function upsertCloudSyncRoom(room, { setActive = true } = {}) {
  const pin = normalizeCloudSyncPin(room?.pin);
  if (pin.length !== CLOUD_SYNC_PIN_LENGTH) return null;
  const id = `${room?.id || createLocalId()}`.trim() || createLocalId();
  const name = `${room?.name || ""}`.trim() || "Playgroup";
  const password = normalizeCloudSyncPassword(room?.password);
  const nextRoom = { id, name, pin, password };
  const existingRooms = getCloudSyncRooms().filter(item => item.id !== id && item.pin !== pin);
  cloudSyncSession = {
    rooms: [nextRoom, ...existingRooms],
    activeRoomId: setActive ? id : (cloudSyncSession?.activeRoomId || id)
  };
  saveCloudSyncSession();
  return nextRoom;
}

function removeCloudSyncRoom(roomId) {
  const nextRooms = getCloudSyncRooms().filter(room => room.id !== roomId);
  const wasActive = `${cloudSyncSession?.activeRoomId || ""}`.trim() === `${roomId || ""}`.trim();
  cloudSyncSession = {
    rooms: nextRooms,
    activeRoomId: !wasActive && nextRooms.some(room => room.id === cloudSyncSession?.activeRoomId)
      ? cloudSyncSession.activeRoomId
      : ""
  };
  saveCloudSyncSession();
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

function createEmptyPersistentGlobalStats() {
  return {
    numberOfMatches: 0,
    totalPlayTime: 0,
    totalTurns: 0,
    numberOfWins: 0,
    totalWinTurns: 0
  };
}

function createEmptyPersistentProfileStats(name = "") {
  return {
    name: `${name || ""}`.trim(),
    numberOfMatches: 0,
    totalPlayTime: 0,
    totalTurns: 0,
    numberOfWins: 0,
    totalWinTurns: 0,
    totalDamage: 0,
    totalHealing: 0,
    enemyScores: {},
    targetScores: {}
  };
}

function createEmptyPersistentStatsStore() {
  return {
    processedEntryKeys: [],
    importedSnapshotsByDevice: {},
    global: createEmptyPersistentGlobalStats(),
    profiles: {}
  };
}

function normalizeNumericScoreMap(scoreMap) {
  const source = scoreMap && typeof scoreMap === "object" ? scoreMap : {};
  return Object.fromEntries(
    Object.entries(source)
      .map(([name, value]) => [`${name || ""}`.trim(), Number.isFinite(value) ? value : 0])
      .filter(([name, value]) => name && value !== 0)
  );
}

function normalizePersistentGlobalStats(stats) {
  return {
    numberOfMatches: Number.isFinite(stats?.numberOfMatches) ? stats.numberOfMatches : 0,
    totalPlayTime: Number.isFinite(stats?.totalPlayTime) ? stats.totalPlayTime : 0,
    totalTurns: Number.isFinite(stats?.totalTurns) ? stats.totalTurns : 0,
    numberOfWins: Number.isFinite(stats?.numberOfWins) ? stats.numberOfWins : 0,
    totalWinTurns: Number.isFinite(stats?.totalWinTurns) ? stats.totalWinTurns : 0
  };
}

function normalizePersistentProfileStats(stats, fallbackName = "") {
  return {
    name: `${stats?.name || fallbackName || ""}`.trim(),
    numberOfMatches: Number.isFinite(stats?.numberOfMatches) ? stats.numberOfMatches : 0,
    totalPlayTime: Number.isFinite(stats?.totalPlayTime) ? stats.totalPlayTime : 0,
    totalTurns: Number.isFinite(stats?.totalTurns) ? stats.totalTurns : 0,
    numberOfWins: Number.isFinite(stats?.numberOfWins) ? stats.numberOfWins : 0,
    totalWinTurns: Number.isFinite(stats?.totalWinTurns) ? stats.totalWinTurns : 0,
    totalDamage: Number.isFinite(stats?.totalDamage) ? stats.totalDamage : 0,
    totalHealing: Number.isFinite(stats?.totalHealing) ? stats.totalHealing : 0,
    enemyScores: normalizeNumericScoreMap(stats?.enemyScores),
    targetScores: normalizeNumericScoreMap(stats?.targetScores)
  };
}

function normalizePersistentStatsSnapshot(snapshot) {
  const sourceProfiles = snapshot?.profiles && typeof snapshot.profiles === "object"
    ? snapshot.profiles
    : {};
  return {
    sourceDeviceId: `${snapshot?.sourceDeviceId || ""}`.trim(),
    global: normalizePersistentGlobalStats(snapshot?.global),
    profiles: Object.fromEntries(
      Object.entries(sourceProfiles)
        .map(([key, value]) => {
          const normalizedKey = normalizeLibraryName(key);
          if (!normalizedKey) return null;
          return [normalizedKey, normalizePersistentProfileStats(value, value?.name || key)];
        })
        .filter(Boolean)
    )
  };
}

function normalizePersistentStatsStore(store) {
  const normalized = createEmptyPersistentStatsStore();
  const source = store && typeof store === "object" ? store : {};
  normalized.processedEntryKeys = Array.isArray(source.processedEntryKeys)
    ? Array.from(new Set(
      source.processedEntryKeys
        .map(value => `${value || ""}`.trim())
        .filter(Boolean)
    ))
    : [];
  normalized.global = normalizePersistentGlobalStats(source.global);

  const sourceProfiles = source.profiles && typeof source.profiles === "object" ? source.profiles : {};
  normalized.profiles = Object.fromEntries(
    Object.entries(sourceProfiles)
      .map(([key, value]) => {
        const normalizedKey = normalizeLibraryName(key);
        if (!normalizedKey) return null;
        return [normalizedKey, normalizePersistentProfileStats(value, value?.name || key)];
      })
      .filter(Boolean)
  );

  const importedSnapshotsByDevice = source.importedSnapshotsByDevice && typeof source.importedSnapshotsByDevice === "object"
    ? source.importedSnapshotsByDevice
    : {};
  normalized.importedSnapshotsByDevice = Object.fromEntries(
    Object.entries(importedSnapshotsByDevice)
      .map(([key, value]) => {
        const deviceKey = `${key || ""}`.trim();
        if (!deviceKey) return null;
        return [deviceKey, normalizePersistentStatsSnapshot(value)];
      })
      .filter(Boolean)
  );

  return normalized;
}

function getPersistentProfileStatsBucket(profileName, createIfMissing = true) {
  const normalizedProfileName = normalizeLibraryName(profileName);
  if (!normalizedProfileName) return null;
  if (!persistentStats.profiles[normalizedProfileName] && createIfMissing) {
    persistentStats.profiles[normalizedProfileName] = createEmptyPersistentProfileStats(profileName);
  }
  const bucket = persistentStats.profiles[normalizedProfileName] || null;
  if (bucket && `${profileName || ""}`.trim()) {
    bucket.name = `${profileName || ""}`.trim();
  }
  return bucket;
}

function applyPersistentGlobalDelta(target, delta) {
  target.numberOfMatches += Number.isFinite(delta?.numberOfMatches) ? delta.numberOfMatches : 0;
  target.totalPlayTime += Number.isFinite(delta?.totalPlayTime) ? delta.totalPlayTime : 0;
  target.totalTurns += Number.isFinite(delta?.totalTurns) ? delta.totalTurns : 0;
  target.numberOfWins += Number.isFinite(delta?.numberOfWins) ? delta.numberOfWins : 0;
  target.totalWinTurns += Number.isFinite(delta?.totalWinTurns) ? delta.totalWinTurns : 0;
}

function applyPersistentProfileDelta(target, delta) {
  target.numberOfMatches += Number.isFinite(delta?.numberOfMatches) ? delta.numberOfMatches : 0;
  target.totalPlayTime += Number.isFinite(delta?.totalPlayTime) ? delta.totalPlayTime : 0;
  target.totalTurns += Number.isFinite(delta?.totalTurns) ? delta.totalTurns : 0;
  target.numberOfWins += Number.isFinite(delta?.numberOfWins) ? delta.numberOfWins : 0;
  target.totalWinTurns += Number.isFinite(delta?.totalWinTurns) ? delta.totalWinTurns : 0;
  target.totalDamage += Number.isFinite(delta?.totalDamage) ? delta.totalDamage : 0;
  target.totalHealing += Number.isFinite(delta?.totalHealing) ? delta.totalHealing : 0;
  Object.entries(normalizeNumericScoreMap(delta?.enemyScores)).forEach(([name, value]) => {
    target.enemyScores[name] = (target.enemyScores[name] || 0) + value;
  });
  Object.entries(normalizeNumericScoreMap(delta?.targetScores)).forEach(([name, value]) => {
    target.targetScores[name] = (target.targetScores[name] || 0) + value;
  });
}

function subtractNumericScoreMaps(nextMap, prevMap) {
  const result = {};
  const allKeys = new Set([
    ...Object.keys(normalizeNumericScoreMap(nextMap)),
    ...Object.keys(normalizeNumericScoreMap(prevMap))
  ]);
  allKeys.forEach((key) => {
    const delta = (Number(nextMap?.[key]) || 0) - (Number(prevMap?.[key]) || 0);
    if (delta !== 0) {
      result[key] = delta;
    }
  });
  return result;
}

/* =========================
   Storage / Persistence
   ========================= */
const deviceId = getOrCreateDeviceId();
let cloudSyncSession = loadCloudSyncSession();

function getWorkspaceStorageKey(baseKey, roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  const normalizedRoomId = `${roomId || ""}`.trim();
  return normalizedRoomId ? `${baseKey}:${normalizedRoomId}` : baseKey;
}

function persistWorkspaceSnapshot(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(PROFILE_STORAGE_KEY, roomId), JSON.stringify(profileLibrary));
  localStorage.setItem(getWorkspaceStorageKey(DECK_STORAGE_KEY, roomId), JSON.stringify(deckLibrary));
  localStorage.setItem(getWorkspaceStorageKey(MATCH_HISTORY_STORAGE_KEY, roomId), JSON.stringify(trimMatchHistoryByCommanderCap(matchHistory)));
  localStorage.setItem(getWorkspaceStorageKey(PERSISTENT_STATS_STORAGE_KEY, roomId), JSON.stringify(persistentStats));
  localStorage.setItem(getWorkspaceStorageKey(SYNC_TOMBSTONES_STORAGE_KEY, roomId), JSON.stringify(normalizeSyncTombstones(syncTombstones)));
  localStorage.setItem(getWorkspaceStorageKey(RESUME_SESSIONS_STORAGE_KEY, roomId), JSON.stringify((Array.isArray(resumeSessions) ? resumeSessions : []).slice(0, 3)));
}

function loadProfileLibrary(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  const parsed = safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(PROFILE_STORAGE_KEY, roomId)), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(item => item && typeof item.id === "string" && typeof item.name === "string")
    .map(item => ({
      ...item,
      lastUsedAt: Number.isFinite(item.lastUsedAt) ? item.lastUsedAt : 0
    }))
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function saveProfileLibrary(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(PROFILE_STORAGE_KEY, roomId), JSON.stringify(profileLibrary));
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

function loadDeckLibrary(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  const parsed = safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(DECK_STORAGE_KEY, roomId)), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(item => {
      if (!item || typeof item.id !== "string") return false;
      const commanderName = `${item.cardName || item.deckName || item.name || ""}`.trim();
      return !!commanderName;
    })
    .map(item => ({
      ...item,
      cardName: `${item.cardName || item.deckName || item.name || ""}`.trim(),
      deckName: `${item.deckName || item.cardName || item.name || ""}`.trim(),
      ownerProfileId: typeof item.ownerProfileId === "string" ? item.ownerProfileId : "",
      artId: typeof item.artId === "string" ? item.artId : "",
      artRef: typeof item.artRef === "string" ? item.artRef : "",
      lastUsedAt: Number.isFinite(item.lastUsedAt) ? item.lastUsedAt : 0
    }))
    .sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
}

function saveDeckLibrary(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(DECK_STORAGE_KEY, roomId), JSON.stringify(deckLibrary));
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

function loadMatchHistory(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  const parsed = safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(MATCH_HISTORY_STORAGE_KEY, roomId)), []);
  if (!Array.isArray(parsed)) return [];
  return trimMatchHistoryByCommanderCap(parsed.map(normalizeMatchHistoryEntry).filter(Boolean));
}

function saveMatchHistory(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  matchHistory = trimMatchHistoryByCommanderCap(matchHistory);
  localStorage.setItem(getWorkspaceStorageKey(MATCH_HISTORY_STORAGE_KEY, roomId), JSON.stringify(matchHistory));
}

function loadPersistentStats(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  return normalizePersistentStatsStore(
    safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(PERSISTENT_STATS_STORAGE_KEY, roomId)), createEmptyPersistentStatsStore())
  );
}

function savePersistentStats(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(PERSISTENT_STATS_STORAGE_KEY, roomId), JSON.stringify(persistentStats));
}

function buildPersistentStatsSnapshot() {
  return {
    sourceDeviceId: deviceId,
    global: normalizePersistentGlobalStats(persistentStats.global),
    profiles: Object.fromEntries(
      Object.entries(persistentStats.profiles)
        .map(([key, value]) => [key, normalizePersistentProfileStats(value, value?.name || key)])
    )
  };
}

function recordPersistentStatsForEntry(entry) {
  const historyKey = getHistoryShareKey(entry);
  if (!historyKey) return false;
  if (persistentStats.processedEntryKeys.includes(historyKey)) return false;

  persistentStats.processedEntryKeys.push(historyKey);
  applyPersistentGlobalDelta(persistentStats.global, {
    numberOfMatches: 1,
    totalPlayTime: Number.isFinite(entry?.totalMatchSeconds) ? entry.totalMatchSeconds : 0,
    totalTurns: Number.isFinite(entry?.turnCount) ? entry.turnCount : 0,
    numberOfWins: Number.isInteger(entry?.winnerIndex) && entry.winnerIndex >= 0 ? 1 : 0,
    totalWinTurns: Number.isInteger(entry?.winnerIndex) && entry.winnerIndex >= 0 && Number.isFinite(entry?.turnCount) ? entry.turnCount : 0
  });

  const playersInEntry = Array.isArray(entry?.players) ? entry.players : [];
  playersInEntry.forEach((player) => {
    const playerName = `${player?.name || ""}`.trim();
    const bucket = getPersistentProfileStatsBucket(playerName);
    if (!bucket) return;

    applyPersistentProfileDelta(bucket, {
      numberOfMatches: 1,
      totalPlayTime: Number.isFinite(player?.totalTime) ? player.totalTime : 0,
      totalTurns: Number.isFinite(entry?.turnCount) ? entry.turnCount : 0,
      numberOfWins: player?.isWinner ? 1 : 0,
      totalWinTurns: player?.isWinner && Number.isFinite(entry?.turnCount) ? entry.turnCount : 0,
      totalDamage: Number.isFinite(player?.stats?.damageDealt) ? player.stats.damageDealt : 0,
      totalHealing: Number.isFinite(player?.stats?.healingDone) ? player.stats.healingDone : 0
    });

    const opponents = playersInEntry.filter(opponent =>
      normalizeLibraryName(opponent?.name) !== normalizeLibraryName(playerName)
    );
    const opponentCount = Math.max(1, opponents.length);
    opponents.forEach((opponent) => {
      const opponentName = `${opponent?.name || ""}`.trim();
      if (!opponentName) return;
      bucket.enemyScores[opponentName] = (bucket.enemyScores[opponentName] || 0) + ((player?.stats?.damageDealt || 0) / opponentCount);
      bucket.targetScores[opponentName] = (bucket.targetScores[opponentName] || 0) + ((opponent?.stats?.damageDealt || 0) / opponentCount);
    });
  });

  savePersistentStats();
  return true;
}

function syncPersistentStatsFromHistory() {
  let changed = false;
  matchHistory.forEach((entry) => {
    if (recordPersistentStatsForEntry(entry)) {
      changed = true;
    }
  });
  if (changed) {
    savePersistentStats();
  }
}

function mergeImportedPersistentStats(statsPayload) {
  const incomingSnapshot = normalizePersistentStatsSnapshot(statsPayload);
  const sourceDeviceId = incomingSnapshot.sourceDeviceId;
  if (!sourceDeviceId || sourceDeviceId === deviceId) return;

  const previousSnapshot = normalizePersistentStatsSnapshot(
    persistentStats.importedSnapshotsByDevice[sourceDeviceId] || {
      sourceDeviceId,
      global: createEmptyPersistentGlobalStats(),
      profiles: {}
    }
  );

  applyPersistentGlobalDelta(persistentStats.global, {
    numberOfMatches: incomingSnapshot.global.numberOfMatches - previousSnapshot.global.numberOfMatches,
    totalPlayTime: incomingSnapshot.global.totalPlayTime - previousSnapshot.global.totalPlayTime,
    totalTurns: incomingSnapshot.global.totalTurns - previousSnapshot.global.totalTurns,
    numberOfWins: incomingSnapshot.global.numberOfWins - previousSnapshot.global.numberOfWins,
    totalWinTurns: incomingSnapshot.global.totalWinTurns - previousSnapshot.global.totalWinTurns
  });

  const allProfileKeys = new Set([
    ...Object.keys(previousSnapshot.profiles),
    ...Object.keys(incomingSnapshot.profiles)
  ]);
  allProfileKeys.forEach((profileKey) => {
    const nextStats = normalizePersistentProfileStats(incomingSnapshot.profiles[profileKey], profileKey);
    const prevStats = normalizePersistentProfileStats(previousSnapshot.profiles[profileKey], profileKey);
    const bucket = getPersistentProfileStatsBucket(nextStats.name || prevStats.name || profileKey);
    if (!bucket) return;
    applyPersistentProfileDelta(bucket, {
      numberOfMatches: nextStats.numberOfMatches - prevStats.numberOfMatches,
      totalPlayTime: nextStats.totalPlayTime - prevStats.totalPlayTime,
      totalTurns: nextStats.totalTurns - prevStats.totalTurns,
      numberOfWins: nextStats.numberOfWins - prevStats.numberOfWins,
      totalWinTurns: nextStats.totalWinTurns - prevStats.totalWinTurns,
      totalDamage: nextStats.totalDamage - prevStats.totalDamage,
      totalHealing: nextStats.totalHealing - prevStats.totalHealing,
      enemyScores: subtractNumericScoreMaps(nextStats.enemyScores, prevStats.enemyScores),
      targetScores: subtractNumericScoreMaps(nextStats.targetScores, prevStats.targetScores)
    });
  });

  persistentStats.importedSnapshotsByDevice[sourceDeviceId] = incomingSnapshot;
  savePersistentStats();
}

function loadResumeSessions(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  const parsed = safeJsonParse(localStorage.getItem(getWorkspaceStorageKey(RESUME_SESSIONS_STORAGE_KEY, roomId)), []);
  if (!Array.isArray(parsed)) return [];
  return parsed
    .filter(entry => entry && typeof entry.id === "string" && entry.snapshot?.hasStartedGame)
    .slice(0, 3);
}

function saveResumeSessions(roomId = `${cloudSyncSession?.activeRoomId || ""}`.trim()) {
  localStorage.setItem(getWorkspaceStorageKey(RESUME_SESSIONS_STORAGE_KEY, roomId), JSON.stringify(resumeSessions.slice(0, 3)));
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
  localStorage.removeItem(getWorkspaceStorageKey(RESUME_SESSIONS_STORAGE_KEY));
}

function clearStoredGameData() {
  matchHistory = [];
  persistentStats = createEmptyPersistentStatsStore();
  syncTombstones = createEmptySyncTombstones();
  clearResumeSessions();
  localStorage.removeItem(getWorkspaceStorageKey(MATCH_HISTORY_STORAGE_KEY));
  localStorage.removeItem(getWorkspaceStorageKey(PERSISTENT_STATS_STORAGE_KEY));
  localStorage.removeItem(getWorkspaceStorageKey(SYNC_TOMBSTONES_STORAGE_KEY));
}

function renderStartScreenBackdrop() {
  const startScreenBg = document.getElementById("start-screen-bg");
  if (!startScreenBg) return;

  const state = ensureSetupState();
  const shouldShowMenuBackdrop =
    !hasStartedGame &&
    !isProfileEditorMode(state) &&
    (state.step === "config" || state.step === "history");
  if (!shouldShowMenuBackdrop) {
    startScreenBg.classList.add("hidden");
    startScreenBg.innerHTML = "";
    return;
  }

  startScreenBg.innerHTML = `
    <div class="start-screen-bg-tile start-screen-bg-tile-full" style="background-image:url('${MENU_BACKGROUND}')"></div>
  `;
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
    isEditingProfile: false,
    editingProfileId: "",
    newProfileName: "",
    hasDuplicateProfileName: false,
    isEditingSeatName: false,
    editingSeatName: "",
    isDeletingProfile: false,
    isAddingDeck: false,
    isEditingDeck: false,
    isEditingDeckArt: false,
    editingDeckId: "",
    editingDeckName: "",
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
    profileEditorMode: false,
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
    qrCloseOnShareExit: false,
    syncRoomId: getActiveCloudSyncRoom()?.id || "",
    syncRoomName: getActiveCloudSyncRoom()?.name || "",
    syncPin: getActiveCloudSyncRoom()?.pin || "",
    syncPassword: getActiveCloudSyncRoom()?.password || "",
    syncConnected: !!getActiveCloudSyncRoom(),
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

function clearSeatDeckSelection(seat, { preserveDeleteMode = false } = {}) {
  if (!seat) return;
  seat.deckId = "";
  seat.deckName = "";
  seat.cardName = "";
  seat.artId = "";
  seat.borrowedFromProfileId = "";
  seat.borrowedFromProfileName = "";
  seat.image = DEFAULT_PLAYER_BACKGROUND;
  seat.isAddingDeck = false;
  if (!preserveDeleteMode) {
    seat.isDeletingDeck = false;
  }
  seat.isBorrowingDeck = false;
  seat.borrowProfileId = "";
  seat.searchQuery = "";
  seat.searchResults = [];
  seat.pendingSearchCard = null;
  seat.searchArtOptions = [];
  seat.isLoadingArtOptions = false;
  seat.isEditingDeck = false;
  seat.isEditingDeckArt = false;
  seat.editingDeckId = "";
  seat.editingDeckName = "";
}

function renameProfileById(profileId, nextName, state = setupState) {
  const profile = profileLibrary.find(item => item.id === profileId);
  const cleanName = `${nextName || ""}`.trim();
  if (!profile || !cleanName) return false;

  const normalizedName = normalizeLibraryName(cleanName);
  const duplicateExists = profileLibrary.some(item =>
    item.id !== profileId && normalizeLibraryName(item.name) === normalizedName
  );
  if (duplicateExists) return false;

  profile.name = cleanName;
  profile.lastUsedAt = Date.now();
  profileLibrary.sort((a, b) => (b.lastUsedAt || 0) - (a.lastUsedAt || 0));
  saveProfileLibrary();

  if (state?.seats) {
    state.seats.forEach((otherSeat) => {
      if (otherSeat?.profileId === profileId) {
        otherSeat.profileName = cleanName;
      }
      if (otherSeat?.borrowProfileId === profileId) {
        otherSeat.borrowedFromProfileName = cleanName;
      }
    });
  }

  return true;
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
  const deletedDeck = deckLibrary[index];
  const deletedDeckOwner = profileLibrary.find(profile => profile.id === deletedDeck?.ownerProfileId);
  const deletedDeckOwnerName = `${deletedDeckOwner?.name || ""}`.trim();
  const deletedCommanderName = `${deletedDeck?.cardName || deletedDeck?.deckName || ""}`.trim();
  recordDeckDeletionTombstone(deletedDeckOwnerName, deletedCommanderName, Date.now());
  deckLibrary.splice(index, 1);
  saveDeckLibrary();

  if (setupState?.seats) {
    setupState.seats.forEach((seat) => {
      if (seat?.deckId === deckId) {
        clearSeatDeckSelection(seat, { preserveDeleteMode: !!seat?.isDeletingDeck });
      }
      if (seat?.isDeletingDeck) {
        const remainingDecksForProfile = deletedDeck?.ownerProfileId
          ? deckLibrary.some(deck => deck.ownerProfileId === deletedDeck.ownerProfileId)
          : deckLibrary.length > 0;
        if (!remainingDecksForProfile) {
          seat.isDeletingDeck = false;
        }
      }
    });
  }

  return true;
}

function deleteProfileById(profileId) {
  if (!profileId) return false;
  const profileIndex = profileLibrary.findIndex(item => item.id === profileId);
  if (profileIndex === -1) return false;
  const deletedProfile = profileLibrary[profileIndex];
  const deletedProfileName = `${deletedProfile?.name || ""}`.trim();
  recordProfileDeletionTombstone(deletedProfileName, Date.now());
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
      if (seat?.isDeletingProfile && profileLibrary.length === 0) {
        seat.isDeletingProfile = false;
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
  triggerHaptic("minimal");
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
  const activePlaygroup = getActiveCloudSyncRoom();
  const playgroupBadgeMarkup = activePlaygroup?.name
    ? `<div class="start-active-playgroup">Playgroup: ${escapeHtml(activePlaygroup.name)}</div>`
    : "";
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
      <button class="setup-start-logo-btn" data-action="debug-clear-cache" aria-label="Clear app cache">
        <img class="setup-start-logo" src="./icons/favicon.png" alt="Life Tracker logo">
      </button>
      <button class="setup-qr-btn setup-icon-circle-btn" data-action="open-qr" aria-label="QR">${getIconMarkup("QR", "setup-inline-icon")}</button>
      <button class="setup-delete-data-btn setup-icon-circle-btn" data-action="delete-game-data" aria-label="Delete stored game data">${getIconMarkup("Delete", "setup-inline-icon")}</button>
      <div class="setup-group" style="margin-top: 20%;">
        <h3 class="start-mode-label">Select Mode</h3>
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
        <button data-action="continue-from-config">Let's play!</button>
        <button class="setup-start-logs-btn" data-action="open-start-logs" aria-label="Game Logs">${getIconMarkup("GameLog", "setup-inline-icon")}</button>
        <button class="setup-start-logs-btn" data-action="open-profile-editor" aria-label="Edit Profiles">${getIconMarkup("Profile", "setup-inline-icon")}</button>
      </div>
      ${jumpBackMarkup}
      ${playgroupBadgeMarkup}
      ${renderQrPanel(state)}
    </div>
  `;
}

function renderQrPanel(state) {
  if (!state?.qrOpen) return "";

  const savedSyncRooms = getCloudSyncRooms();
  const selectedSyncRoomId = getActiveCloudSyncRoomId(state);
  const status = (state.qrStatus || "").trim();
  const isMenu = state.qrView === "menu";
  const shouldShowMenuImportStatus = isMenu && /^Imported\s/i.test(status);
  const statusMarkup = status && (!isMenu || shouldShowMenuImportStatus)
    ? `<div class="qr-status">${escapeHtml(status)}</div>`
    : "";
  const isShare = state.qrView === "share";
  const isScan = state.qrView === "scan";
  const isSync = state.qrView === "sync";
  const showBackdrop = isShare && !!state.qrImageUrl;
  const shareExitAction = state.qrCloseOnShareExit ? "close-qr" : "back-qr-menu";
  const shareExitIcon = state.qrCloseOnShareExit ? "Cancel" : "Back";
  const shareExitLabel = state.qrCloseOnShareExit ? "Close" : "Back";
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
            <button data-action="open-qr-sync">Sync</button>
          </div>
        ` : ""}
        ${isShare ? `
          <div class="qr-share-body">
            ${state.qrImageUrl ? `<img class="qr-image" src="${state.qrImageUrl}" alt="Transfer QR">` : `<div class="qr-placeholder">QR too large, use Copy Code.</div>`}
            <textarea class="qr-payload" readonly>${escapeHtml(state.qrSharePayload || "")}</textarea>
            <div class="setup-footer qr-menu-actions qr-menu-actions-inline">
              <button class="setup-icon-circle-btn qr-back-btn" data-action="${shareExitAction}" aria-label="${shareExitLabel}">${getIconMarkup(shareExitIcon, "setup-inline-icon")}</button>
              <button data-action="copy-qr-payload">Copy</button>
            </div>
          </div>
        ` : ""}
        ${isScan ? `
          <div class="qr-scan-body">
            <video id="qr-scan-video" class="qr-scan-video" autoplay playsinline muted></video>
            <textarea class="qr-payload" data-qr-input="scan-payload" placeholder="Paste your Code here if camera is unavailable.">${escapeHtml(state.qrInput || "")}</textarea>
            <div class="setup-footer qr-menu-actions qr-menu-actions-inline">
              <button class="setup-icon-circle-btn qr-back-btn" data-action="${shareExitAction}" aria-label="${shareExitLabel}">${getIconMarkup(shareExitIcon, "setup-inline-icon")}</button>
              <button data-action="import-qr-payload">Import</button>
              </div>
          </div>
        ` : ""}
        ${isSync ? `
          <div class="qr-scan-body">
            <select class="sync-payload sync-highlight" data-sync-room-select="room">
              <option value="">New playgroup</option>
              ${savedSyncRooms.map((room) => `<option value="${escapeHtml(room.id)}" ${selectedSyncRoomId === room.id ? "selected" : ""}>${escapeHtml(room.name)}</option>`).join("")}
            </select>
            <input class="sync-payload" data-sync-room-name="room-name" maxlength="40" value="${escapeHtml(state.syncRoomName || "")}" placeholder="Playgroup name">
            <input class="sync-payload" type="password" data-sync-pin="room-pin" inputmode="numeric" maxlength="${CLOUD_SYNC_PIN_LENGTH}" value="${escapeHtml(state.syncPin || "")}" placeholder="4-digit room PIN">
            <input class="sync-payload" type="password" data-sync-password="room-password" inputmode="numeric" maxlength="${CLOUD_SYNC_PIN_LENGTH}" value="${escapeHtml(state.syncPassword || "")}" placeholder="4-digit room password">
            <div class="setup-footer qr-menu-actions qr-menu-actions-inline">
              <button class="setup-icon-circle-btn qr-back-btn" data-action="back-qr-menu" aria-label="Back">${getIconMarkup("Back", "setup-inline-icon")}</button>
              <button data-action="join-sync-room">Join</button>
              ${state.syncConnected ? `<button class="setup-icon-circle-btn qr-back-btn" data-action="disconnect-sync-room" aria-label="Leave sync room">${getIconMarkup("Delete", "setup-inline-icon")}</button>` : ""}
            </div>
          </div>
        ` : ""}
      </div>
    </div>
  `;
}

function normalizeCommanderArtRef(value) {
  const raw = `${value || ""}`.trim().replace(/^\/+|\/+$/g, "");
  const customMatch = raw.match(/^custom\/([a-z0-9-]+)$/i);
  if (customMatch) return `/custom/${customMatch[1].toLowerCase()}/`;
  const scryfallMatch = raw.match(/^([a-z0-9]{2,8})\/([a-z0-9]+)$/i);
  if (!scryfallMatch) return "";
  return `/${scryfallMatch[1].toLowerCase()}/${scryfallMatch[2].toLowerCase()}/`;
}

function getDeckTransferArtRef(deck) {
  return normalizeCommanderArtRef(deck?.artRef) || normalizeCommanderArtRef(deck?.artId);
}

function buildScryfallArtCropUrlFromRef(ref) {
  const normalizedRef = normalizeCommanderArtRef(ref);
  if (!normalizedRef) return "";
  const [setCode, collectorNumber] = normalizedRef.replace(/^\/+|\/+$/g, "").split("/");
  if (setCode === "custom") {
    return CUSTOM_COMMANDER_ARTS.find((item) => {
      if (item.artRef === normalizedRef) return true;
      const legacyRef = item.artRef.replace(/1\/$/, "/");
      return legacyRef === normalizedRef;
    })?.art || "";
  }
  if (!setCode || !collectorNumber) return "";
  return `https://api.scryfall.com/cards/${encodeURIComponent(setCode)}/${encodeURIComponent(collectorNumber)}?format=image&version=art_crop`;
}

function getCustomCommanderArtOptions(name) {
  const normalizedName = normalizeLibraryName(name);
  if (!normalizedName) return [];
  return CUSTOM_COMMANDER_ARTS
    .filter((item) => normalizeLibraryName(item.commanderName) === normalizedName)
    .map((item, index) => ({
      id: `custom-${index}-${normalizedName}`,
      printId: "",
      artRef: item.artRef,
      art: item.art,
      setLabel: item.setLabel
    }));
}

function buildQrTransferBundle(includeGames = false) {
  const decksByOwner = new Map();
  deckLibrary.forEach((deck) => {
    if (deck?.mode && deck.mode !== "commander") return;
    const ownerId = `${deck?.ownerProfileId || ""}`.trim();
    if (!ownerId) return;
    const commanderName = `${deck?.cardName || deck?.deckName || ""}`.trim();
    const customDeckName = `${deck?.deckName || ""}`.trim();
    if (!commanderName) return;
    if (!decksByOwner.has(ownerId)) {
      decksByOwner.set(ownerId, []);
    }
    decksByOwner.get(ownerId).push({
      name: commanderName,
      commanderName,
      deckName: customDeckName || commanderName,
      artRef: getDeckTransferArtRef(deck),
      lastUsedAt: Number.isFinite(deck?.lastUsedAt) ? deck.lastUsedAt : 0
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
  const historyEntries = includeGames
    ? commanderGames
        .map(entry => normalizeMatchHistoryEntry(entry))
        .filter(Boolean)
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
            commanderName: deck.commanderName,
            deckName: deck.deckName,
            artRef: deck.artRef
          }));
        return {
          name,
          lastUsedAt: Number.isFinite(profile?.lastUsedAt) ? profile.lastUsedAt : 0,
          decks
        };
      })
      .filter(Boolean),
    games,
    historyEntries,
    stats: buildPersistentStatsSnapshot(),
    tombstones: normalizeSyncTombstones(syncTombstones)
  };
}

function buildProfileQrTransferBundle(profileId) {
  const profile = profileLibrary.find(item => item?.id === profileId);
  const profileName = `${profile?.name || ""}`.trim();
  if (!profileName) {
    return {
      profiles: [],
      games: []
    };
  }

  const decks = deckLibrary
    .filter(deck => deck?.mode === "commander" && deck?.ownerProfileId === profileId)
    .map((deck) => {
      const commanderName = `${deck?.cardName || deck?.deckName || ""}`.trim();
      const customDeckName = `${deck?.deckName || commanderName}`.trim() || commanderName;
      return {
        name: commanderName,
        commanderName,
        deckName: customDeckName,
        ownerProfileName: profileName,
        artRef: getDeckTransferArtRef(deck),
        lastUsedAt: Number.isFinite(deck?.lastUsedAt) ? deck.lastUsedAt : 0
      };
    })
    .filter(deck => deck.name);

  return {
    profiles: [
      {
        name: profileName,
        lastUsedAt: Number.isFinite(profile?.lastUsedAt) ? profile.lastUsedAt : 0,
        decks
      }
    ],
    games: []
  };
}

function encodeQrTransferPayload(bundle) {
  return `${QR_TRANSFER_PREFIX}${toBase64Utf8(JSON.stringify(bundle))}`;
}

function getActiveCloudSyncRoomId(state = setupState) {
  const roomId = `${state?.syncRoomId || cloudSyncSession?.activeRoomId || ""}`.trim();
  return roomId || "";
}

function getCloudSyncRoomById(roomId) {
  return getCloudSyncRooms().find(room => room.id === roomId) || null;
}

function getActiveCloudSyncRoom(state = setupState) {
  const roomId = getActiveCloudSyncRoomId(state);
  return getCloudSyncRoomById(roomId) || getCloudSyncRoomById(cloudSyncSession?.activeRoomId || "") || null;
}

function getPendingCloudSyncRoom(state = setupState) {
  const roomId = getActiveCloudSyncRoomId(state);
  const storedRoom = getCloudSyncRoomById(roomId);
  const pin = normalizeCloudSyncPin(state?.syncPin || storedRoom?.pin || "");
  const name = `${state?.syncRoomName || storedRoom?.name || ""}`.trim() || "Playgroup";
  const password = normalizeCloudSyncPassword(state?.syncPassword || storedRoom?.password || "");
  return {
    id: roomId || storedRoom?.id || "",
    name,
    pin,
    password
  };
}

function setCloudSyncStatus(message, { shouldRender = true } = {}) {
  const state = ensureSetupState();
  state.qrStatus = `${message || ""}`.trim();
  const activeRoom = getCloudSyncRoomById(getActiveCloudSyncRoomId(state)) || getActiveCloudSyncRoom();
  state.syncRoomId = activeRoom?.id || state.syncRoomId || "";
  state.syncRoomName = activeRoom?.name || state.syncRoomName || "";
  state.syncPin = normalizeCloudSyncPin(state.syncPin || activeRoom?.pin || "");
  state.syncPassword = normalizeCloudSyncPassword(state.syncPassword || activeRoom?.password || "");
  state.syncConnected = !!activeRoom;
  if (shouldRender && state.qrOpen && state.qrView === "sync") {
    renderStartSetupScreen();
  }
}

function markCloudSyncPending() {
  if (!getActiveCloudSyncRoom()) return;
  cloudSyncPending = true;
}

function stopCloudSyncLoop({ clearSession = false, clearRoomId = "", status = "" } = {}) {
  const previousRoomId = `${cloudSyncSession?.activeRoomId || ""}`.trim();
  if (cloudSyncLoopId !== null) {
    window.clearInterval(cloudSyncLoopId);
    cloudSyncLoopId = null;
  }
  cloudSyncInFlightPromise = null;
  if (clearSession) {
    if (previousRoomId) {
      persistWorkspaceSnapshot(previousRoomId);
    }
    if (clearRoomId) {
      removeCloudSyncRoom(clearRoomId);
    } else {
      cloudSyncSession = { rooms: [], activeRoomId: "" };
      saveCloudSyncSession();
    }
    loadWorkspaceSnapshot("", { shouldRender: false });
  }
  const state = ensureSetupState();
  if (clearSession) {
    state.syncRoomId = getActiveCloudSyncRoom()?.id || "";
    state.syncRoomName = getActiveCloudSyncRoom()?.name || "";
    state.syncPin = "";
    state.syncPassword = "";
  }
  state.syncConnected = !!getActiveCloudSyncRoom();
  if (status) {
    setCloudSyncStatus(status);
  }
}

async function syncCloudRoom(roomOrPin, { silent = false } = {}) {
  const room = typeof roomOrPin === "string"
    ? { pin: roomOrPin, name: "", id: "", password: "" }
    : (roomOrPin || getPendingCloudSyncRoom());
  const normalizedPin = normalizeCloudSyncPin(room?.pin);
  const normalizedPassword = normalizeCloudSyncPassword(room?.password);
  if (normalizedPin.length !== CLOUD_SYNC_PIN_LENGTH) {
    if (!silent) setCloudSyncStatus("Enter a 4-digit PIN.");
    return null;
  }
  if (normalizedPassword.length !== CLOUD_SYNC_PIN_LENGTH) {
    if (!silent) setCloudSyncStatus("Enter a 4-digit password.");
    return null;
  }
  if (typeof navigator !== "undefined" && navigator.onLine === false) {
    markCloudSyncPending();
    if (!silent) setCloudSyncStatus("Offline. Sync will retry when online.");
    return null;
  }
  if (cloudSyncInFlightPromise) return cloudSyncInFlightPromise;

  cloudSyncInFlightPromise = (async () => {
    const response = await fetch(`/api/sync/${encodeURIComponent(normalizedPin)}/sync`, {
      method: "POST",
      headers: {
        "content-type": "application/json"
      },
      body: JSON.stringify({
        deviceId,
        password: normalizedPassword,
        bundle: buildQrTransferBundle(true)
      })
    });
    if (!response.ok) {
      throw new Error(
        response.status === 401
          ? "Wrong room password."
          : response.status === 404
            ? "Room not found."
            : "Cloud sync failed."
      );
    }
    const payload = await response.json();
    const merged = mergeImportedTransferData(payload?.bundle || {});
    const nextRoom = upsertCloudSyncRoom({
      id: room?.id || "",
      name: room?.name || "",
      pin: normalizedPin,
      password: normalizedPassword
    }, { setActive: true });
    const state = ensureSetupState();
    state.syncRoomId = nextRoom?.id || "";
    state.syncRoomName = nextRoom?.name || "";
    state.syncPin = normalizedPin;
    state.syncPassword = normalizedPassword;
    state.syncConnected = true;
    cloudSyncPending = false;
    if (!silent) {
      const imported = (merged?.addedProfiles || 0) + (merged?.addedDecks || 0) + (merged?.addedGames || 0);
      setCloudSyncStatus(imported > 0 ? `Synced ${nextRoom?.name || "room"}. Imported ${imported} item${imported === 1 ? "" : "s"}.` : `Synced ${nextRoom?.name || "room"}.`);
    }
    return payload;
  })();

  try {
    return await cloudSyncInFlightPromise;
  } catch (error) {
    markCloudSyncPending();
    if (!silent) {
      setCloudSyncStatus(error instanceof Error ? error.message : "Cloud sync failed.");
    }
    throw error;
  } finally {
    cloudSyncInFlightPromise = null;
  }
}

function startCloudSyncLoop(roomOrPin, { syncNow = true, silent = false } = {}) {
  const room = typeof roomOrPin === "string"
    ? { pin: roomOrPin, name: "", id: "", password: "" }
    : (roomOrPin || getPendingCloudSyncRoom());
  const normalizedPin = normalizeCloudSyncPin(room?.pin);
  const normalizedPassword = normalizeCloudSyncPassword(room?.password);
  if (normalizedPin.length !== CLOUD_SYNC_PIN_LENGTH) return;
  if (normalizedPassword.length !== CLOUD_SYNC_PIN_LENGTH) return;
  stopCloudSyncLoop();
  const nextRoom = activateCloudSyncWorkspace(room, { shouldRender: false });
  const state = ensureSetupState();
  state.syncRoomId = nextRoom?.id || "";
  state.syncRoomName = nextRoom?.name || "";
  state.syncPin = normalizedPin;
  state.syncPassword = normalizedPassword;
  state.syncConnected = true;
  if (syncNow) {
    void syncCloudRoom(nextRoom || room, { silent });
  }
  cloudSyncLoopId = window.setInterval(() => {
    void syncCloudRoom(nextRoom || room, { silent: true });
  }, CLOUD_SYNC_POLL_MS);
}

function syncActiveCloudRoom({ silent = true } = {}) {
  const activeRoom = getActiveCloudSyncRoom();
  if (!activeRoom) return;
  if (typeof navigator !== "undefined" && navigator.onLine === false) {
    markCloudSyncPending();
    return;
  }
  startCloudSyncLoop(activeRoom, { syncNow: false, silent: true });
  void syncCloudRoom(activeRoom, { silent });
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
  const urls = [fuzzyUrl, exactUrl];

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
  const urls = [fuzzyUrl, exactUrl];

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
  const importedHistoryEntries = Array.isArray(payload.historyEntries)
    ? payload.historyEntries.map(entry => normalizeMatchHistoryEntry(entry)).filter(Boolean)
    : [];
  mergeSyncTombstones(payload.tombstones);
  applySyncTombstonesToLocalData();

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
    const incomingLastUsedAt = Number.isFinite(incoming?.lastUsedAt) ? incoming.lastUsedAt : 0;
    if (getLatestProfileDeletion(incomingName) >= incomingLastUsedAt) return;
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
    const commanderName = `${incomingDeck?.commanderName || incomingDeck?.name || ""}`.trim();
    if (!commanderName) return;
    const importedDeckName = `${incomingDeck?.deckName || incomingDeck?.customName || commanderName}`.trim() || commanderName;
    const hasImportedCustomDeckName = normalizeLibraryName(importedDeckName) !== normalizeLibraryName(commanderName);
    const incomingImage = `${incomingDeck?.image || ""}`.trim();
    const incomingArtId = normalizeCommanderArtId(incomingDeck?.artId);
    const incomingArtRef = normalizeCommanderArtRef(incomingDeck?.artRef || incomingDeck?.artId);
    const resolvedIncomingImage = incomingImage || buildScryfallArtCropUrlFromRef(incomingArtRef);
    const incomingLastUsedAt = Number.isFinite(incomingDeck?.lastUsedAt) ? incomingDeck.lastUsedAt : 0;

    // Owner name is authoritative for cross-device merging.
    let ownerProfileId = "";
    const ownerName = `${incomingDeck?.ownerProfileName || ""}`.trim();
    if (ownerName) {
      ownerProfileId = ensureProfileIdByName(ownerName);
    }
    if (!ownerProfileId) return;
    if (getLatestProfileDeletion(ownerName) >= incomingLastUsedAt) return;
    if (getLatestDeckDeletion(ownerName, commanderName) >= incomingLastUsedAt) return;

    const existingDeck = deckLibrary.find(deck =>
      deck.ownerProfileId === ownerProfileId &&
      normalizeLibraryName(deck.cardName || deck.deckName) === normalizeLibraryName(commanderName)
    );
    if (existingDeck) {
      if (!existingDeck.cardName) {
        existingDeck.cardName = commanderName;
      }
      const existingDeckName = `${existingDeck.deckName || ""}`.trim();
      const existingCommanderName = `${existingDeck.cardName || commanderName}`.trim();
      const existingHasCustomDeckName =
        existingDeckName &&
        normalizeLibraryName(existingDeckName) !== normalizeLibraryName(existingCommanderName);
      if (!existingHasCustomDeckName && hasImportedCustomDeckName) {
        existingDeck.deckName = importedDeckName;
      }
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
      deckName: importedDeckName,
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
  const existingHistoryIndexByKey = new Map(
    matchHistory
      .map((entry, index) => [`${entry?.sourceEntryId || entry?.id || ""}`.trim(), index])
      .filter(([key]) => key)
  );

  const shouldReplaceImportedHistory = (currentEntry, incomingEntry) => {
    if (!currentEntry) return true;
    const currentLogLength = Array.isArray(currentEntry?.gameLog) ? currentEntry.gameLog.length : 0;
    const incomingLogLength = Array.isArray(incomingEntry?.gameLog) ? incomingEntry.gameLog.length : 0;
    if (incomingLogLength !== currentLogLength) return incomingLogLength > currentLogLength;
    const currentActions = Number.isFinite(currentEntry?.actionCount) ? currentEntry.actionCount : 0;
    const incomingActions = Number.isFinite(incomingEntry?.actionCount) ? incomingEntry.actionCount : 0;
    if (incomingActions !== currentActions) return incomingActions > currentActions;
    const currentTurns = Number.isFinite(currentEntry?.turnCount) ? currentEntry.turnCount : 0;
    const incomingTurns = Number.isFinite(incomingEntry?.turnCount) ? incomingEntry.turnCount : 0;
    if (incomingTurns !== currentTurns) return incomingTurns > currentTurns;
    return (incomingEntry?.endedAt || 0) >= (currentEntry?.endedAt || 0);
  };

  importedHistoryEntries.forEach((incomingEntry) => {
    const sourceEntryId = `${incomingEntry?.sourceEntryId || incomingEntry?.id || ""}`.trim();
    if (!sourceEntryId) return;
    const existingIndex = existingHistoryIndexByKey.get(sourceEntryId);
    if (existingIndex === undefined) {
      matchHistory.push(incomingEntry);
      existingHistoryIndexByKey.set(sourceEntryId, matchHistory.length - 1);
      existingHistoryKeys.add(sourceEntryId);
      addedGames += 1;
      return;
    }
    const currentEntry = matchHistory[existingIndex];
    if (!shouldReplaceImportedHistory(currentEntry, incomingEntry)) return;
    matchHistory[existingIndex] = incomingEntry;
  });

  if (!importedHistoryEntries.length) importedGames.forEach((incomingGame) => {
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
  const incomingStatsPayloads = Array.isArray(payload.stats)
    ? payload.stats
    : (payload.stats ? [payload.stats] : []);
  if (incomingStatsPayloads.length) {
    incomingStatsPayloads.forEach((statsSnapshot) => {
      mergeImportedPersistentStats(statsSnapshot);
    });
  } else {
    syncPersistentStatsFromHistory();
  }

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
    !isProfileEditorMode(state) &&
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
        <button class="setup-plus-btn" data-action="add-profile" data-seat="${playerIndex}" aria-label="Add profile">${getIconMarkup("Plus", "setup-inline-icon setup-plus-icon")}</button>
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
        <button class="setup-plus-btn" data-action="add-deck" data-seat="${playerIndex}" aria-label="Add deck">${getIconMarkup("Plus", "setup-inline-icon setup-plus-icon")}</button>
        <input type="text" data-seat-input="deckName" data-seat="${playerIndex}" value="${seat.deckName || ""}" placeholder="Deck name">
        <input type="text" data-seat-deck-search="${playerIndex}" placeholder="Search commander">
        <div class="setup-search-results" data-seat-search-results="${playerIndex}"></div>
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
  const currentEditingDeck = seat.isEditingDeck
    ? profileDecks.find(deck => deck.id === seat.editingDeckId) || null
    : null;
  const borrowProfiles = profileLibrary.filter(profile => profile.id !== seat.profileId);
  const borrowProfileName = borrowProfiles.find(profile => profile.id === seat.borrowProfileId)?.name || "";
  const borrowDecks = getDecksForProfile(seat.borrowProfileId);
  const visibleDecks = seat.isBorrowingDeck ? borrowDecks : profileDecks;

  const hasProfile = !!(seat.profileId && (seat.profileName || "").trim());
  const hasDeck = !!(seat.deckId && (seat.cardName || "").trim() && (seat.image || "").trim());
  const allowBorrowDeck = selectedPlayerCount > 1;
  const isSingleSeatEditor = isSingleSeatProfileEditorMode();
  const keepSingleSeatDeckLayout = isSingleSeatEditor && hasProfile && !seat.isBorrowingDeck && !seat.isAddingDeck && !seat.isEditingDeckArt;
  const artStyle = hasDeck ? `style="background-image:url('${seat.image.replace(/'/g, "\\'")}')"` : "";
  const selectedDeckName = getSeatDeckLabel(seat);
  const historySummaryStats = isSingleSeatEditor ? buildMatchSummaryStats() : null;
  const profileStats = isSingleSeatEditor ? buildProfileHistoryStats(seat.profileName) : null;
  const profileStatsMarkup = isSingleSeatEditor && hasProfile && !seat.isBorrowingDeck && !seat.isAddingDeck && !seat.isEditingDeckArt
    ? renderStatsSummaryGrid([
      { label: "Number of Matches", value: String(profileStats.numberOfMatches) },
      { label: "Total Play Time", value: formatTime(profileStats.totalPlayTime) },
      { label: "Number of Wins", value: String(profileStats.numberOfWins) },
      { label: "Average Turn Time", value: formatAverageDuration(profileStats.averageTurnTime) },
      { label: "Average Turn Win", value: formatAverageTurnWin(profileStats.averageTurnWin) },
      { label: "Total Damage", value: String(profileStats.totalDamage) },
      { label: "Total Healing", value: String(profileStats.totalHealing) },
      { label: "Your Enemy", value: profileStats.enemy || "-" },
      { label: "Target Of", value: profileStats.targetOf || "-" }
    ], "setup-profile-stats-grid")
    : "";
  const backButton = `
    <button class="setup-seat-back-btn" data-action="go-back-profile-seat" data-seat="${playerIndex}" aria-label="Back to player selection">
      ${getIconMarkup("Back", "setup-back-icon")}
    </button>
  `;

  if (!hasProfile) {
    const profileAction = seat.isDeletingProfile
      ? "delete-profile"
      : seat.isEditingProfile
        ? "select-edit-profile"
        : "select-profile";
    const canDeleteProfiles = profileLibrary.length > 0;
    const profileButtons = profileLibrary.length
      ? `
        <div class="setup-profile-list">
          ${profileLibrary.map(profile => `
            <button class="setup-profile-btn ${(seat.isEditingProfile ? seat.editingProfileId : seat.profileId) === profile.id ? "active" : ""} ${seat.isDeletingProfile ? "is-delete-mode" : ""}" data-action="${profileAction}" data-seat="${playerIndex}" data-profile-id="${profile.id}" ${!seat.isDeletingProfile && !seat.isEditingProfile && isProfileSelectedInOtherSeat(state, profile.id, playerIndex) ? "disabled" : ""}>
              ${profile.name}
            </button>
          `).join("")}
        </div>
      `
      : `<div class="setup-meta">No profiles yet.</div>`;

    const addProfilePanel = seat.isAddingProfile
      ? `
        <div class="setup-add-profile-panel">
          <input type="text" class="${seat.hasDuplicateProfileName ? "setup-input-invalid" : ""}" data-seat-input="newProfileName" data-seat="${playerIndex}" value="${seat.newProfileName || ""}" placeholder="Player name">
          <button data-action="${seat.isEditingProfile ? "save-profile-edit" : "create-profile"}" data-seat="${playerIndex}" ${seat.hasDuplicateProfileName ? "disabled" : ""}>${seat.isEditingProfile ? "Save" : "Create"}</button>
        </div>
      `
      : "";

    return `
      <div class="setup-seat-overlay ${seat.isAddingProfile ? "setup-seat-overlay-searching" : ""} ${isSingleSeatEditor && !seat.isAddingProfile && !seat.isEditingProfile ? "setup-profile-picker-mode" : ""}">
        ${seat.isAddingProfile || seat.isEditingProfile ? `
          ${backButton.replace("go-back-profile-seat", seat.isEditingProfile ? "close-edit-profile" : "close-add-profile").replace("Back to player selection", seat.isEditingProfile ? "Back from profile editing" : "Back from profile creation")}
          <div class="setup-seat-header">
            <div class="setup-seat-title">${seat.isEditingProfile ? "Edit Player" : "New Player"}</div>
          </div>
          ${addProfilePanel}
        ` : `
          ${isSingleSeatEditor
            ? backButton
                .replace("go-back-profile-seat", "back-to-config")
                .replace(
                  'aria-label="Back to player selection"',
                  `aria-label="${seat.isDeletingProfile ? "Back disabled while deleting profiles" : seat.isEditingSeatName ? "Back disabled while editing player name" : "Back to config"}"${seat.isDeletingProfile || seat.isEditingSeatName ? " disabled" : ""}`
                )
            : ""}
          ${isSingleSeatEditor ? `
            <div class="setup-seat-header">
              <div class="setup-seat-title-row">
                <div class="setup-seat-title">${seat.isDeletingProfile ? "Delete Profile" : seat.isEditingProfile ? "EDIT PLAYER" : "View Profile"}</div>
              </div>
            </div>
          ` : `<div class="setup-seat-title">${seat.isDeletingProfile ? "Delete Profile" : seat.isEditingProfile ? "EDIT PLAYER" : "Select Profile"}</div>`}
          ${isSingleSeatEditor ? renderStatsSummaryGrid([
            { label: "Number of Matches", value: String(historySummaryStats.numberOfMatches) },
            { label: "Total Play Time", value: formatTime(historySummaryStats.totalPlayTime) },
            { label: "Average Game Time", value: formatAverageDuration(historySummaryStats.averageGameTime) },
            { label: "Average Turn Time", value: formatAverageDuration(historySummaryStats.averageTurnTime) },
            { label: "Average Turn Win", value: formatAverageTurnWin(historySummaryStats.averageTurnWin) }
          ], "setup-profile-picker-stats") : ""}
          ${profileButtons}
          <button class="${isSingleSeatEditor ? "setup-plus-btn" : "setup-minus-btn"}" data-action="add-profile" data-seat="${playerIndex}" aria-label="Add profile" ${seat.isDeletingProfile ? "disabled" : ""}>${getIconMarkup("Plus", "setup-inline-icon setup-plus-icon")}</button>
          ${canDeleteProfiles && isSingleSeatEditor ? `<button class="setup-minus-btn ${seat.isDeletingProfile ? "active" : ""}" data-action="${seat.isDeletingProfile ? "close-delete-profile" : "open-delete-profile"}" data-seat="${playerIndex}" aria-label="Delete player mode">${getIconMarkup("Delete", "setup-inline-icon")}</button>` : ""}
        `}
      </div>
    `;
  }

  const canInteractWithDeckGrid = seat.isDeletingDeck || seat.isEditingDeck || seat.isBorrowingDeck || !isSingleSeatEditor;
  const deckAction = seat.isDeletingDeck
    ? "delete-deck"
    : seat.isEditingDeck
      ? "select-edit-deck"
      : !canInteractWithDeckGrid
        ? ""
        : "select-deck";
  const canDeleteDecks = profileDecks.length > 0;
  const deckGrid = visibleDecks.length
    ? `
      <div class="setup-deck-grid ${seat.isBorrowingDeck ? "setup-deck-grid-full" : ""} ${seat.isEditingDeck ? "is-edit-mode" : ""} ${seat.isEditingDeck && seat.editingDeckId ? "has-selection" : ""}">
        ${visibleDecks.map(deck => {
          const isUnavailable = !seat.isDeletingDeck && isDeckSelectedInOtherSeat(state, deck.id, playerIndex);
          const isActiveDeck = seat.isEditingDeck
            ? seat.editingDeckId === deck.id
            : seat.deckId === deck.id;
          const isDisabledDeckThumb = isUnavailable;
          const isPassiveDeckThumb = !canInteractWithDeckGrid;
          return `
          <button class="setup-deck-thumb ${isActiveDeck ? "active" : ""} ${seat.isDeletingDeck ? "is-delete-mode" : ""} ${seat.isEditingDeck ? "is-edit-mode" : ""} ${isUnavailable ? "is-unavailable" : ""} ${isPassiveDeckThumb ? "is-passive" : ""}" ${deckAction ? `data-action="${deckAction}"` : ""} data-seat="${playerIndex}" data-deck-id="${deck.id}" ${isDisabledDeckThumb ? "disabled" : ""}>
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
            <input type="text" data-seat-deck-search="${playerIndex}" value="${escapeHtml(seat.searchQuery || "")}" placeholder="Search commander">
            <div class="setup-search-results" data-seat-search-results="${playerIndex}"></div>
          `
        }
      </div>
    `
    : "";

  const deckEditPanel = seat.isEditingDeck
    ? `
      <div class="setup-add-deck-panel">
        ${seat.isEditingDeckArt
          ? `
            <div class="setup-art-choice-header">
              <div class="setup-meta">Choose art for ${escapeHtml((currentEditingDeck?.cardName || seat.editingDeckName || "").trim())}</div>
            </div>
            ${seat.isLoadingArtOptions
              ? `<div class="setup-meta">Loading print arts...</div>`
              : `
                ${(seat.searchArtOptions || []).length
                  ? `
                    <div class="setup-search-art-grid">
                      ${(seat.searchArtOptions || []).map((option) => `
                        <button class="setup-search-art-thumb" data-action="select-search-art" data-seat="${playerIndex}" data-art-id="${escapeHtml(option.id)}">
                          <img src="${option.art}" alt="${escapeHtml(currentEditingDeck?.cardName || seat.editingDeckName || "Commander art")}">
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
            <div class="setup-meta setup-deck-edit-copy">Select a deck to edit, then update its custom name or card art.</div>
            ${seat.editingDeckId ? `
              <div class="setup-deck-name-editor">
                <input type="text" data-seat-input="editingDeckName" data-seat="${playerIndex}" value="${escapeHtml(seat.editingDeckName || "")}" placeholder="Deck name">
                <button class="setup-seat-name-save-btn" data-action="save-deck-edit" data-seat="${playerIndex}" aria-label="Save deck name">
                  ${getIconMarkup("Ok", "setup-inline-icon")}
                </button>
              </div>
              <div class="setup-footer">
                <button data-action="open-edit-deck-art" data-seat="${playerIndex}">Change Art</button>
              </div>
            ` : `<div class="setup-meta setup-deck-edit-copy">Choose a deck first.</div>`}
            ${deckGrid}
          `
        }
      </div>
    `
    : "";

  const inlineDeckEditPanel = seat.isEditingDeck && seat.editingDeckId && !seat.isEditingDeckArt
    ? `
      <div class="setup-add-deck-panel">
        <div class="setup-meta setup-deck-edit-copy">Select a deck to edit, then update its custom name or card art.</div>
        <div class="setup-deck-name-editor">
          <input type="text" data-seat-input="editingDeckName" data-seat="${playerIndex}" value="${escapeHtml(seat.editingDeckName || "")}" placeholder="Deck name">
          <button class="setup-seat-name-save-btn" data-action="save-deck-edit" data-seat="${playerIndex}" aria-label="Save deck name">
            ${getIconMarkup("Ok", "setup-inline-icon")}
          </button>
        </div>
        <div class="setup-footer">
          <button data-action="open-edit-deck-art" data-seat="${playerIndex}">Change Art</button>
        </div>
      </div>
    `
    : (seat.isEditingDeck && !seat.isEditingDeckArt
      ? `<div class="setup-meta setup-deck-edit-copy">Select a deck to edit, then update its custom name or card art.</div>`
      : "");

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
    : seat.isEditingDeck
    ? `
      <button class="setup-seat-back-btn" data-action="${seat.isEditingDeckArt ? "close-edit-deck-art" : "close-edit-deck"}" data-seat="${playerIndex}" aria-label="Back from deck edit">
        ${getIconMarkup("Back", "setup-back-icon")}
      </button>
    `
    : backButton;
  const renderedDeckBackButton = (seat.isDeletingDeck || seat.isEditingDeck)
    ? deckBackButton
        .replace(
          '<button class="setup-seat-back-btn"',
          `<button class="setup-seat-back-btn"${seat.isEditingDeck ? ' data-edit-locked="1"' : ""} disabled`
        )
        .replace(
          /aria-label="[^"]*"/,
          `aria-label="${seat.isEditingDeck ? "Back disabled while editing decks" : "Back disabled while deleting decks"}"`
        )
    : deckBackButton;

  return `
    <div class="setup-seat-overlay ${hasDeck ? "setup-seat-ready" : ""} ${(seat.isAddingDeck || seat.isEditingDeckArt) ? "setup-seat-overlay-searching" : ""} ${seat.isEditingDeck && !seat.isEditingDeckArt ? "setup-seat-overlay-editing-deck" : ""}">
      ${renderedDeckBackButton}
      <div class="setup-seat-header">
        ${keepSingleSeatDeckLayout
          ? (
            seat.isEditingSeatName
              ? `
                <div class="setup-seat-name-editor is-active">
                  <input type="text" data-seat-input="editingSeatName" data-seat="${playerIndex}" value="${escapeHtml(seat.editingSeatName || "")}" placeholder="Player name">
                  <button class="setup-seat-name-save-btn" data-action="save-seat-name" data-seat="${playerIndex}" aria-label="Save player name">
                    ${getIconMarkup("Ok", "setup-inline-icon")}
                  </button>
                </div>
              `
              : `
                <div class="setup-seat-title-row">
                  <div class="setup-seat-title setup-seat-title-selected">${seat.isDeletingDeck ? "Delete Deck" : escapeHtml(seat.profileName)}</div>
                  ${seat.isDeletingDeck || seat.isEditingDeck ? "" : `
                    <div class="setup-seat-title-actions">
                      <button class="setup-seat-title-edit-btn" data-action="open-edit-seat-name" data-seat="${playerIndex}" aria-label="Edit player name">
                        ${getIconMarkup("Edit", "setup-inline-icon")}
                      </button>
                      <button class="setup-seat-title-qr-btn" data-action="open-profile-qr-share" data-seat="${playerIndex}" aria-label="Share profile decks as QR">
                        ${getIconMarkup("QR", "setup-inline-icon")}
                      </button>
                    </div>
                  `}
                </div>
              `
          )
          : `<div class="setup-seat-title ${(!seat.isBorrowingDeck && !seat.isAddingDeck) ? "setup-seat-title-selected" : ""}">${seat.isAddingDeck ? "Add a Deck" : seat.isBorrowingDeck ? `Borrow Deck${seat.borrowProfileId ? ` from ${borrowProfileName}` : ""}` : seat.isEditingDeck ? "Edit Deck" : escapeHtml(seat.profileName)}</div>`
        }
        ${(isSingleSeatEditor || seat.isAddingDeck || seat.isBorrowingDeck || seat.isEditingDeck) ? "" : (selectedDeckName ? `<div class="setup-meta setup-seat-subtitle">${selectedDeckName}</div>` : "")}
      </div>
      ${profileStatsMarkup}
      ${seat.isAddingDeck ? addPanel : (seat.isEditingDeck && !keepSingleSeatDeckLayout) ? deckEditPanel : seat.isBorrowingDeck ? borrowPanel : `
        ${inlineDeckEditPanel}
        <div class="setup-seat-body">
          ${deckGrid}
        </div>
        <button class="${isSingleSeatEditor ? "setup-plus-btn" : "setup-minus-btn"}" data-action="add-deck" data-seat="${playerIndex}" aria-label="Add deck" ${seat.isDeletingDeck || seat.isEditingDeck ? "disabled" : ""}>${getIconMarkup("Plus", "setup-inline-icon setup-plus-icon")}</button>
        ${!isSingleSeatEditor ? "" : `<button class="setup-edit-btn ${seat.isEditingDeck ? "active" : ""}" data-action="${seat.isEditingDeck ? "close-edit-deck" : "open-edit-deck"}" data-seat="${playerIndex}" aria-label="Edit deck" ${seat.isDeletingDeck ? "disabled" : ""}>${getIconMarkup("Edit", "setup-inline-icon")}</button>`}
        ${canDeleteDecks && isSingleSeatEditor ? `<button class="setup-minus-btn ${seat.isDeletingDeck ? "active" : ""} ${seat.isEditingDeck ? "is-disabled" : ""}" data-action="${seat.isDeletingDeck ? "close-delete-deck" : "open-delete-deck"}" data-seat="${playerIndex}" aria-label="Delete deck mode" ${seat.isEditingDeck ? "disabled" : ""}>${getIconMarkup("Delete", "setup-inline-icon")}</button>` : ""}
        ${!allowBorrowDeck ? "" : `<button class="setup-borrow-btn" data-action="open-borrow-deck" data-seat="${playerIndex}" aria-label="Borrow deck" ${seat.isDeletingDeck || seat.isEditingDeck ? "disabled" : ""}>Borrow</button>`}
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
    const isSingleSeatEditor = isSingleSeatProfileEditorMode();
    p.life = state.startingLife;
    p.name = (seat.profileName || "").trim() || `Player ${index + 1}`;
    p.commander = state.mode === "magic" ? "" : ((seat.cardName || "").trim());
    p.commanderArtId = state.mode === "magic" ? "" : normalizeCommanderArtId(seat.artId);
    p.image = isSingleSeatEditor
      ? (getSingleSeatEditorBackgroundImage(state, index) || getSeatBackgroundImage(seat, index, state.mode))
      : getSeatBackgroundImage(seat, index, state.mode);
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
    playerEl.classList.toggle("setup-seat-outlined", !useBoardStarterSelection);
    if (!useBoardStarterSelection) {
      info.innerHTML = renderCommanderSeatOverlay(state, playerIndex);
      bindSetupSeatBodyDrag(playerEl, playerIndex);
      updateScrollableFadeState(info);
      syncSetupDeckGridMetrics(info);
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
  } else if (!hasAnySelectedProfile(state) && !isSingleSeatProfileEditorMode()) {
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
  syncSetupDeckGridMetrics(document);
}

function syncSetupSeatPreviewPlayer(state, seatIndex) {
  const seat = state?.seats?.[seatIndex] || getDefaultSeatState(seatIndex);
  const player = players[seatIndex];
  if (!player) return;
  player.life = state?.startingLife || player.life;
  player.name = (seat.profileName || "").trim() || `Player ${seatIndex + 1}`;
  player.commander = state?.mode === "magic" ? "" : ((seat.cardName || "").trim());
  player.commanderArtId = state?.mode === "magic" ? "" : normalizeCommanderArtId(seat?.artId);
  player.image = isSingleSeatProfileEditorMode()
    ? (getSingleSeatEditorBackgroundImage(state, seatIndex) || getSeatBackgroundImage(seat, seatIndex, state?.mode))
    : getSeatBackgroundImage(seat, seatIndex, state?.mode);
}

function refreshSetupSeatOverlay(seatIndex) {
  if (!setupGridPreviewActive) return false;
  const state = ensureSetupState();
  if (!isProfileEditorMode(state) && (shouldUseBoardStarterSelection(state) || (allSetupSeatsReady(state) && !state.forceDeckSelection))) {
    renderStartSetupScreen();
    return true;
  }

  syncSetupSeatPreviewPlayer(state, seatIndex);
  const playerEl = document.getElementById(`player${seatIndex}`);
  const info = playerEl?.querySelector(".info_container");
  const bg = playerEl?.querySelector(".bg");
  if (!playerEl || !info || !bg) return false;

  playerEl.classList.add("setup-seat-player");
  playerEl.classList.toggle("setup-seat-outlined", !shouldUseBoardStarterSelection(state));
  info.innerHTML = renderCommanderSeatOverlay(state, seatIndex);
  bg.style.backgroundImage = players[seatIndex].image ? `url(${players[seatIndex].image})` : "none";
  bindSetupSeatBodyDrag(playerEl, seatIndex);
  updateScrollableFadeState(info);
  syncSetupDeckGridMetrics(info);
  refreshSetupArtGridLayout(info);
  updateCommanderOverlayAnchors();
  return true;
}

function updateScrollableFadeState(root = document) {
  const updateScrollFade = (el) => {
    if (!el) return;
    const isScrollable = (el.scrollHeight - el.clientHeight) > 2;
    const isScrolled = el.scrollTop > 2;
    el.classList.toggle("is-scrollable", isScrollable);
    el.classList.toggle("is-scrolled", isScrollable && isScrolled);
    el.classList.toggle("is-bottomed", !isScrollable || (el.scrollTop + el.clientHeight >= el.scrollHeight - 2));
  };

  const apply = () => {
    root.querySelectorAll(".setup-profile-list, .history-list, .history-detail-shell, .game-log-list").forEach((list) => {
      updateScrollFade(list);
      if (list.dataset.fadeBound === "1") return;
      list.dataset.fadeBound = "1";
      list.addEventListener("scroll", () => updateScrollFade(list), { passive: true });
    });
    root.querySelectorAll(".setup-seat-body, .setup-deck-grid").forEach((el) => {
      updateScrollFade(el);
      if (el.dataset.fadeBound === "1") return;
      el.dataset.fadeBound = "1";
      el.addEventListener("scroll", () => updateScrollFade(el), { passive: true });
    });
  };

  apply();
  window.requestAnimationFrame(apply);
}

function syncSetupDeckGridMetrics(root = document) {
  const grids = Array.from(root.querySelectorAll(".setup-deck-grid"));
  if (!grids.length) return;

  const measureGrid = (grid) => {
    const firstThumb = grid.querySelector(".setup-deck-thumb");
    if (!firstThumb) {
      grid.style.removeProperty("--setup-deck-row-size");
      return;
    }
    const width = firstThumb.getBoundingClientRect().width;
    if (width > 0) grid.style.setProperty("--setup-deck-row-size", `${width}px`);
  };

  grids.forEach((grid) => {
    measureGrid(grid);
    if (grid.dataset.sizeBound === "1") return;
    grid.dataset.sizeBound = "1";

    if ("ResizeObserver" in window) {
      const observer = new ResizeObserver(() => measureGrid(grid));
      observer.observe(grid);
      const firstThumb = grid.querySelector(".setup-deck-thumb");
      if (firstThumb) observer.observe(firstThumb);
    }

    grid.querySelectorAll("img").forEach((img) => {
      if (img.complete) return;
      img.addEventListener("load", () => measureGrid(grid), { once: true });
    });
  });
}

function refreshSetupArtGridLayout(root = document) {
  const grids = Array.from(
    root.querySelectorAll('#game[data-players="1"] .player.single-seat-editor .setup-add-deck-panel .setup-search-art-grid, .player.single-seat-editor .setup-add-deck-panel .setup-search-art-grid')
  );
  if (!grids.length) return;

  grids.forEach((grid) => {
    const rerenderGrid = () => {
      const scrollTop = grid.scrollTop;
      const previousDisplay = grid.style.display;
      grid.style.display = "none";
      void grid.offsetHeight;
      grid.style.display = previousDisplay || "grid";
      grid.scrollTop = scrollTop;
    };

    window.requestAnimationFrame(() => {
      rerenderGrid();
      window.requestAnimationFrame(rerenderGrid);
    });

    grid.querySelectorAll("img").forEach((img) => {
      if (img.complete) return;
      img.addEventListener("load", () => {
        window.requestAnimationFrame(rerenderGrid);
      }, { once: true });
    });
  });
}

function bindSetupSeatBodyDrag(playerEl, seatIndex) {
  const scrollers = playerEl
    ? Array.from(playerEl.querySelectorAll(".setup-seat-body, .setup-search-results, .setup-profile-list, .setup-deck-grid, .setup-search-art-grid"))
        .filter((scroller) => {
          if (!scroller.classList.contains("setup-seat-body")) return true;
          return !scroller.querySelector(".setup-search-results, .setup-profile-list, .setup-deck-grid, .setup-search-art-grid");
        })
    : [];
  if (!scrollers.length) return;

  const seatRotation = getSeatRotation(selectedPlayerCount, seatIndex);
  const usesSidewaysDrag = Math.abs(seatRotation) === 90;
  scrollers.forEach((scroller) => {
    const isRailScroller =
      scroller.classList.contains("setup-profile-list")
      || scroller.classList.contains("setup-deck-grid")
      || scroller.classList.contains("setup-search-results")
      || scroller.classList.contains("setup-search-art-grid");
    bindDragScroll(scroller, {
      usesSidewaysDrag,
      seatRotation,
      reverseSidewaysDrag: usesSidewaysDrag && isRailScroller && seatRotation < 0,
      ignoreSelectors: "input, select"
    });
  });
}

function bindDragScroll(scroller, { usesSidewaysDrag = false, seatRotation = 0, reverseSidewaysDrag = false, ignoreSelectors = "" } = {}) {
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
      // Deck grids visually read in the opposite direction from the other rotated setup scrollers.
      scroller.scrollTop = startScrollTop + (reverseSidewaysDrag ? -deltaX : deltaX);
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
  pauseBtn.classList.add("hidden");
  pauseBtn.classList.remove("active");
  setPauseButtonIcon(false);
  document.body.classList.toggle("profile-editor-open", isProfileEditorMode(state));
  document.body.classList.toggle("profile-editor-qr-open", isProfileEditorMode(state) && !!state.qrOpen);
  document.body.classList.toggle("history-open", state.step === "history");
  renderStartScreenBackdrop();
  startScreen.classList.remove("hidden");
  container.classList.remove("hidden");
  startScreen.classList.add("setup-open");

  if (state.step === "config") {
    if (!hasStartedGame) {
      selectedPlayerCount = 0;
      game.dataset.players = "0";
      document.body.dataset.players = "0";
    }
    exitSetupGridPreview();
    container.innerHTML = renderStartConfigStep(state);
  } else if (state.step === "history") {
    stopQrScanner();
    state.qrOpen = false;
    if (!hasStartedGame) {
      selectedPlayerCount = 0;
      game.dataset.players = "0";
      document.body.dataset.players = "0";
    }
    exitSetupGridPreview();
    container.innerHTML = renderStartHistoryScreen();
  } else if (state.step === "seats") {
    stopQrScanner();
    renderCommanderGridOnGame(state);
    container.innerHTML = renderQrPanel(state);
    state.seats.forEach((seat, index) => {
      renderSearchResults(index, seat?.searchResults || [], seat?.searchQuery || "");
    });
  } else {
    stopQrScanner();
    state.qrOpen = false;
    exitSetupGridPreview();
    container.innerHTML = pendingDuelContinuation
      ? renderStartingPlayerStep(state, { backAction: "back-from-duel-next-starter" })
      : renderStartingPlayerStep(state);
  }

  updateScrollableFadeState(container);
  syncSetupDeckGridMetrics(document);
  refreshSetupArtGridLayout(document);
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
  const url = `https://api.scryfall.com/cards/autocomplete?q=${encodeURIComponent(clean)}`;
  const controller = new AbortController();
  const timeoutId = window.setTimeout(() => controller.abort(), SCRYFALL_SEARCH_TIMEOUT_MS);
  try {
    const response = await fetch(url, { signal: controller.signal });
    if (!response.ok) return [];
    const payload = await response.json();
    const names = Array.isArray(payload.data) ? payload.data.filter(Boolean).slice(0, 12) : [];
    if (!names.length) return [];

    const cards = await Promise.all(names.map(async (name) => {
      const namedUrl = `https://api.scryfall.com/cards/named?exact=${encodeURIComponent(name)}`;
      try {
        const namedResponse = await fetch(namedUrl, { signal: controller.signal });
        if (!namedResponse.ok) return null;
        return await namedResponse.json();
      } catch {
        return null;
      }
    }));

    return cards
      .filter(card => card && (!commanderOnly || isCommanderEligibleCard(card)))
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
  const customOptions = getCustomCommanderArtOptions(card.name);
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

    const mergedOptions = [...customOptions, ...options];
    if (!mergedOptions.length) return fallback;
    return mergedOptions;
  } catch {
    return [...customOptions, ...fallback];
  }
}

async function clearPwaCacheForDebug() {
  const keepKeys = new Set([
    PROFILE_STORAGE_KEY,
    DECK_STORAGE_KEY,
    MATCH_HISTORY_STORAGE_KEY,
    PERSISTENT_STATS_STORAGE_KEY
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
    await Promise.all(cacheKeys.map(async (key) => {
      try {
        const cache = await caches.open(key);
        const requests = await cache.keys();
        await Promise.all(
          requests
            .filter((request) => {
              try {
                return new URL(request.url).pathname.includes("/custom-art/");
              } catch {
                return false;
              }
            })
            .map((request) => cache.delete(request))
        );
      } catch {
        // Ignore per-cache custom-art cleanup failures and continue.
      }
    }));
    await Promise.all(cacheKeys.map((key) => caches.delete(key)));
  }

  if ("serviceWorker" in navigator) {
    const registrations = await navigator.serviceWorker.getRegistrations();
    await Promise.all(registrations.map((registration) => registration.unregister()));
  }
}

function renderSearchResults(seatIndex, cards, query = "") {
  const resultEls = Array.from(document.querySelectorAll(`[data-seat-search-results="${seatIndex}"]`));
  const state = ensureSetupState();
  const seat = state.seats[seatIndex];
  seat.searchResults = Array.isArray(cards) ? cards : [];
  seat.searchQuery = `${query || ""}`;
  resultEls.forEach((resultsEl) => {
    resultsEl.replaceChildren(...buildSearchResultNodes(seatIndex, seat.searchResults, seat.searchQuery));
  });
}

function buildSearchResultNodes(seatIndex, cards, query = "") {
  const state = ensureSetupState();
  const seat = state.seats[seatIndex];
  const cleanQuery = `${query || ""}`.trim();
  if (!cards.length) {
    if (!seat?.isAddingDeck || cleanQuery.length < 2) {
      return [];
    }
    const isDuplicateForPlayer = profileAlreadyHasDeck(seat.profileId, cleanQuery);
    return [buildSearchResultButton({
      seatIndex,
      action: "create-default-search-deck",
      disabled: isDuplicateForPlayer,
      datasetKey: "deckName",
      datasetValue: cleanQuery,
      image: DEFAULT_PLAYER_BACKGROUND,
      name: cleanQuery,
      typeLine: navigator.onLine ? "No online match found. Create locally." : "Offline mode. Create locally with default art.",
      exact: false,
      badges: ["Default Deck"].concat(isDuplicateForPlayer ? ["Added"] : [])
    })];
  }
  return cards.map(card => {
    const isDuplicateForPlayer = profileAlreadyHasDeck(seat?.profileId, card.name);
    return buildSearchResultButton({
      seatIndex,
      action: "select-search-card",
      disabled: isDuplicateForPlayer,
      datasetKey: "cardId",
      datasetValue: card.id,
      image: card.art,
      name: card.name,
      typeLine: card.typeLine,
      exact: !!card.exact,
      badges: isDuplicateForPlayer ? ["Added"] : []
    });
  });
}

function buildSearchResultButton({ seatIndex, action, disabled = false, datasetKey = "", datasetValue = "", image = "", name = "", typeLine = "", exact = false, badges = [] }) {
  const button = document.createElement("button");
  button.className = `search-result${disabled ? " search-result-disabled" : ""}`;
  button.dataset.action = action;
  button.dataset.seat = String(seatIndex);
  if (datasetKey) {
    button.dataset[datasetKey] = `${datasetValue || ""}`;
  }
  if (disabled) {
    button.disabled = true;
  }

  const img = document.createElement("img");
  img.src = `${image || ""}`;
  img.alt = "";
  button.appendChild(img);

  const copy = document.createElement("span");
  copy.className = "search-result-copy";

  const nameRow = document.createElement("span");
  nameRow.className = "search-result-name-row";

  const nameEl = document.createElement("span");
  nameEl.className = "search-result-name";
  nameEl.textContent = `${name || ""}`;
  nameRow.appendChild(nameEl);

  if (exact) {
    const exactBadge = document.createElement("span");
    exactBadge.className = "search-result-badge";
    exactBadge.textContent = "Exact";
    nameRow.appendChild(exactBadge);
  }

  badges.forEach((badgeText) => {
    const badge = document.createElement("span");
    badge.className = "search-result-badge search-result-badge-muted";
    badge.textContent = `${badgeText || ""}`;
    nameRow.appendChild(badge);
  });

  const meta = document.createElement("span");
  meta.className = "search-result-meta";
  meta.textContent = `${typeLine || ""}`;

  copy.appendChild(nameRow);
  copy.appendChild(meta);
  button.appendChild(copy);
  return button;
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
    triggerHaptic("minimal");

    if (action === "set-mode") {
      state.mode = btn.dataset.mode === "magic" ? "magic" : "commander";
      if (state.mode === "magic") {
        state.playerCount = 2;
        state.matchLength = normalizeDuelMatchLength(state.matchLength);
        state.startingLife = 20;
        if (state.startingPlayerIndex > 1) state.startingPlayerIndex = 0;
      } else {
        state.playerCount = 4;
        if (state.startingLife === 20) {
          state.startingLife = 40;
        }
        state.startingPlayerIndex = Math.min(state.startingPlayerIndex, state.playerCount - 1);
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

    if (action === "delete-game-data") {
      btn.disabled = true;
      btn.textContent = "Deleting...";
      clearStoredGameData();
      renderStartSetupScreen();
      return;
    }

    if (action === "open-qr") {
      state.qrOpen = true;
      state.qrView = "menu";
      state.qrStatus = "";
      state.qrInput = "";
      state.qrCloseOnShareExit = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-qr") {
      stopQrScanner();
      state.qrOpen = false;
      state.qrView = "menu";
      state.qrInput = "";
      state.qrCloseOnShareExit = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "back-qr-menu") {
      stopQrScanner();
      state.qrView = "menu";
      state.qrInput = "";
      state.qrCloseOnShareExit = false;
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
      state.qrCloseOnShareExit = false;
      state.qrStatus = hasQrImage
        ? "Share player and deck names with a QR code. Alternatively use the text code."
        : "Data is too large for a single QR code. Use Copy.";
      renderStartSetupScreen();
      return;
    }

    if (action === "open-profile-qr-share" && Number.isInteger(seat)) {
      const seatState = state.seats?.[seat];
      const profileId = `${seatState?.profileId || ""}`.trim();
      if (!profileId) return;
      await hydrateMissingDeckArtRefs({ limit: 100 });
      const transferBundle = buildProfileQrTransferBundle(profileId);
      const transferPayload = encodeQrTransferPayload(transferBundle);
      const qrDataUrl = buildLocalQrDataUrl(transferPayload);
      const hasQrImage = !!qrDataUrl;

      state.qrOpen = true;
      state.qrView = "share";
      state.qrSharePayload = transferPayload;
      state.qrDisplayPayload = transferPayload;
      state.qrImageUrl = qrDataUrl;
      state.qrCloseOnShareExit = true;
      state.qrStatus = hasQrImage
        ? "Share this profile's decks and custom deck names with a QR code."
        : "Data is too large for a single QR code. Use Copy.";
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
      state.qrCloseOnShareExit = false;
      renderStartSetupScreen();
      void startQrScanner();
      return;
    }

    if (action === "open-qr-sync") {
      const activeRoom = getActiveCloudSyncRoom();
      state.qrOpen = true;
      state.qrView = "sync";
      state.syncRoomId = activeRoom?.id || "";
      state.syncRoomName = activeRoom?.name || state.syncRoomName || "";
      state.syncPin = activeRoom?.pin || state.syncPin || "";
      state.syncPassword = activeRoom?.password || state.syncPassword || "";
      state.syncConnected = !!activeRoom;
      state.qrStatus = activeRoom
        ? `Connected to ${activeRoom.name}.`
        : "Create or join a 4-digit sync room with a 4-digit password.";
      renderStartSetupScreen();
      return;
    }

    if (action === "join-sync-room") {
      const pendingRoom = getPendingCloudSyncRoom(state);
      try {
        if (pendingRoom.password.length !== CLOUD_SYNC_PIN_LENGTH) {
          throw new Error("Enter a 4-digit password.");
        }
        let createdNewRoom = false;
        if (pendingRoom.pin.length === CLOUD_SYNC_PIN_LENGTH) {
          const response = await fetch(`/api/sync/${encodeURIComponent(pendingRoom.pin)}/ensure`, {
            method: "POST",
            headers: {
              "content-type": "application/json"
            },
            body: JSON.stringify({
              password: pendingRoom.password
            })
          });
          if (!response.ok) {
            throw new Error(response.status === 401 ? "Wrong room password." : "Unable to open that room.");
          }
          const payload = await response.json();
          createdNewRoom = !!payload?.created;
        } else {
          const response = await fetch("/api/sync/create", {
            method: "POST",
            headers: {
              "content-type": "application/json"
            },
            body: JSON.stringify({
              password: pendingRoom.password
            })
          });
          if (!response.ok) throw new Error("Unable to create room.");
          const payload = await response.json();
          const pin = normalizeCloudSyncPin(payload?.pin || "");
          if (pin.length !== CLOUD_SYNC_PIN_LENGTH) throw new Error("Invalid room response.");
          pendingRoom.pin = pin;
          createdNewRoom = true;
        }
        startCloudSyncLoop(pendingRoom, { syncNow: false });
        await syncCloudRoom(pendingRoom);
        if (pendingRoom.name) {
          state.qrStatus = createdNewRoom
            ? `Created ${pendingRoom.name}.`
            : `Connected to ${pendingRoom.name}.`;
        }
      } catch (error) {
        stopCloudSyncLoop({
          clearSession: true,
          clearRoomId: pendingRoom.id || getActiveCloudSyncRoom()?.id || "",
          status: error instanceof Error ? error.message : "Unable to open that room."
        });
      }
      renderStartSetupScreen();
      return;
    }

    if (action === "disconnect-sync-room") {
      const activeRoom = getActiveCloudSyncRoom(state);
      stopCloudSyncLoop({
        clearSession: true,
        clearRoomId: activeRoom?.id || "",
        status: activeRoom ? `${activeRoom.name} removed from this device.` : "Sync room cleared on this device."
      });
      state.qrView = "sync";
      renderStartSetupScreen();
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

    if (action === "open-profile-editor") {
      state.mode = "commander";
      state.playerCount = 1;
      state.step = "seats";
      state.startingPlayerIndex = 0;
      state.profileEditorMode = true;
      state.showStarterPicker = false;
      state.forceDeckSelection = true;
      if (state.startingLife === 20) {
        state.startingLife = 40;
      }
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
      renderStartSetupScreen();
      return;
    }

    if (action === "continue-from-config") {
      state.profileEditorMode = false;
      state.step = "seats";
      state.showStarterPicker = false;
      state.forceDeckSelection = state.mode === "commander";
      renderStartSetupScreen();
      return;
    }

    if (action === "back-to-config") {
      state.profileEditorMode = false;
      state.step = "config";
      if (state.mode === "commander") {
        state.playerCount = 4;
        if (state.startingLife === 20) {
          state.startingLife = 40;
        }
      }
      state.showStarterPicker = false;
      state.forceDeckSelection = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-edit-seat-name" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.isEditingSeatName = true;
      seatState.editingSeatName = (seatState.profileName || "").trim();
      renderStartSetupScreen();
      return;
    }

    if (action === "save-seat-name" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      const profileId = seatState.profileId || "";
      const name = (seatState.editingSeatName || "").trim();
      if (!profileId || !name) return;
      if (!renameProfileById(profileId, name, state)) {
        return;
      }
      seatState.isEditingSeatName = false;
      seatState.editingSeatName = "";
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
      state.seats[seat].isEditingProfile = false;
      state.seats[seat].editingProfileId = "";
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

    if (action === "open-edit-profile" && Number.isInteger(seat)) {
      state.seats[seat].isEditingProfile = true;
      state.seats[seat].isAddingProfile = true;
      state.seats[seat].isDeletingProfile = false;
      state.seats[seat].editingProfileId = "";
      state.seats[seat].newProfileName = "";
      state.seats[seat].hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-edit-profile" && Number.isInteger(seat)) {
      state.seats[seat].isEditingProfile = false;
      state.seats[seat].isAddingProfile = false;
      state.seats[seat].editingProfileId = "";
      state.seats[seat].newProfileName = "";
      state.seats[seat].hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-delete-profile" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingProfile = true;
      state.seats[seat].isAddingProfile = false;
      state.seats[seat].isEditingProfile = false;
      state.seats[seat].editingProfileId = "";
      renderStartSetupScreen();
      return;
    }

    if (action === "close-delete-profile" && Number.isInteger(seat)) {
      state.seats[seat].isDeletingProfile = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "select-edit-profile" && Number.isInteger(seat)) {
      const profileId = btn.dataset.profileId || "";
      const profile = profileLibrary.find(item => item.id === profileId);
      if (!profile) return;
      state.seats[seat].editingProfileId = profile.id;
      state.seats[seat].newProfileName = profile.name;
      state.seats[seat].hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "delete-profile" && Number.isInteger(seat)) {
      const profileId = btn.dataset.profileId || "";
      if (!deleteProfileById(profileId)) return;
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

    if (action === "save-profile-edit" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      const profileId = seatState.editingProfileId || "";
      const name = (seatState.newProfileName || "").trim();
      if (!profileId || !name) return;
      if (!renameProfileById(profileId, name, state)) {
        seatState.hasDuplicateProfileName = true;
        renderStartSetupScreen();
        return;
      }
      seatState.isEditingProfile = false;
      seatState.isAddingProfile = false;
      seatState.editingProfileId = "";
      seatState.newProfileName = "";
      seatState.hasDuplicateProfileName = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-edit-deck" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.isEditingDeck = true;
      seatState.isEditingDeckArt = false;
      seatState.isAddingDeck = false;
      seatState.isDeletingDeck = false;
      seatState.isBorrowingDeck = false;
      seatState.borrowProfileId = "";
      seatState.editingDeckId = "";
      seatState.editingDeckName = "";
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "close-edit-deck" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.isEditingDeck = false;
      seatState.isEditingDeckArt = false;
      seatState.deckId = "";
      seatState.deckName = "";
      seatState.cardName = "";
      seatState.artId = "";
      seatState.borrowedFromProfileId = "";
      seatState.borrowedFromProfileName = "";
      seatState.image = DEFAULT_PLAYER_BACKGROUND;
      seatState.editingDeckId = "";
      seatState.editingDeckName = "";
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "select-edit-deck" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      const deckId = btn.dataset.deckId || "";
      const deck = deckLibrary.find(item => item.id === deckId && item.ownerProfileId === seatState.profileId);
      if (!deck) return;
      seatState.deckId = deck.id;
      seatState.deckName = deck.deckName || "";
      seatState.cardName = deck.cardName || "";
      seatState.artId = normalizeCommanderArtId(deck.artId);
      seatState.borrowedFromProfileId = "";
      seatState.borrowedFromProfileName = "";
      seatState.image = deck.image || DEFAULT_PLAYER_BACKGROUND;
      seatState.editingDeckId = deck.id;
      seatState.editingDeckName = deck.deckName || deck.cardName || "";
      seatState.isEditingDeckArt = false;
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "save-deck-edit" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      const deckId = seatState.editingDeckId || "";
      const deck = deckLibrary.find(item => item.id === deckId && item.ownerProfileId === seatState.profileId);
      const nextDeckName = (seatState.editingDeckName || "").trim();
      if (!deck || !nextDeckName) return;
      deck.deckName = nextDeckName;
      deck.lastUsedAt = Date.now();
      saveDeckLibrary();
      if (seatState.deckId === deck.id) {
        seatState.deckName = deck.deckName;
      }
      seatState.isEditingDeck = false;
      seatState.isEditingDeckArt = false;
      seatState.deckId = "";
      seatState.deckName = "";
      seatState.cardName = "";
      seatState.artId = "";
      seatState.borrowedFromProfileId = "";
      seatState.borrowedFromProfileName = "";
      seatState.image = DEFAULT_PLAYER_BACKGROUND;
      seatState.editingDeckId = "";
      seatState.editingDeckName = "";
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
      renderStartSetupScreen();
      return;
    }

    if (action === "open-edit-deck-art" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      const deckId = seatState.editingDeckId || "";
      const deck = deckLibrary.find(item => item.id === deckId && item.ownerProfileId === seatState.profileId);
      if (!deck) return;
      seatState.isEditingDeckArt = true;
      seatState.pendingSearchCard = {
        id: normalizeCommanderArtId(deck.artId) || deck.id,
        name: deck.cardName || deck.deckName || "",
        art: deck.image || "",
        printsUri: ""
      };
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = true;
      renderStartSetupScreen();
      const selectedCardId = seatState.pendingSearchCard.id;
      const artOptions = await fetchCommanderPrintArts(seatState.pendingSearchCard);
      if (!seatState.isEditingDeck || !seatState.isEditingDeckArt) return;
      if (!seatState.pendingSearchCard || seatState.pendingSearchCard.id !== selectedCardId) return;
      seatState.searchArtOptions = artOptions;
      seatState.isLoadingArtOptions = false;
      void warmCommanderImageCacheUrls(artOptions.map(option => option.art));
      renderStartSetupScreen();
      return;
    }

    if (action === "close-edit-deck-art" && Number.isInteger(seat)) {
      const seatState = state.seats[seat];
      seatState.isEditingDeckArt = false;
      seatState.pendingSearchCard = null;
      seatState.searchArtOptions = [];
      seatState.isLoadingArtOptions = false;
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
      state.forceDeckSelection = isProfileEditorMode(state) ? true : false;
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
      state.seats[seat].isDeletingDeck = getDecksForProfile(state.seats[seat].profileId).length > 0;
      state.seats[seat].isBorrowingDeck = false;
      state.seats[seat].borrowProfileId = "";
      state.forceDeckSelection = isProfileEditorMode(state) ? true : !allSetupSeatsReady(state);
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
      state.forceDeckSelection = isProfileEditorMode(state) ? true : false;
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
        state.forceDeckSelection = isProfileEditorMode(state) ? true : false;
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
      if (!seatState.profileId || !seatState.pendingSearchCard) return;
      const artId = btn.dataset.artId || "";
      const selectedArt = (seatState.searchArtOptions || []).find(option => option.id === artId);
      if (seatState.isEditingDeck && seatState.isEditingDeckArt) {
        const deckId = seatState.editingDeckId || "";
        const deck = deckLibrary.find(item => item.id === deckId && item.ownerProfileId === seatState.profileId);
        if (!deck) return;
        deck.artId = normalizeCommanderArtId(selectedArt?.printId || seatState.pendingSearchCard.id);
        deck.artRef = normalizeCommanderArtRef(selectedArt?.artRef);
        deck.image = selectedArt?.art || seatState.pendingSearchCard.art || deck.image;
        deck.lastUsedAt = Date.now();
        void warmCommanderImageCacheUrls([deck.image]);
        saveDeckLibrary();
        if (seatState.deckId === deck.id) {
          seatState.artId = deck.artId;
          seatState.image = deck.image;
        }
        seatState.isEditingDeckArt = false;
        seatState.pendingSearchCard = null;
        seatState.searchArtOptions = [];
        seatState.isLoadingArtOptions = false;
        renderStartSetupScreen();
        return;
      }
      if (!seatState.isAddingDeck) return;
      if (profileAlreadyHasDeck(seatState.profileId, seatState.pendingSearchCard.name)) {
        return;
      }
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
      state.forceDeckSelection = isProfileEditorMode(state) ? true : false;
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

    const syncPinInput = event.target.closest("[data-sync-pin]");
    if (syncPinInput) {
      state.syncPin = normalizeCloudSyncPin(syncPinInput.value || "");
      return;
    }

    const syncPasswordInput = event.target.closest("[data-sync-password]");
    if (syncPasswordInput) {
      state.syncPassword = normalizeCloudSyncPassword(syncPasswordInput.value || "");
      return;
    }

    const syncRoomNameInput = event.target.closest("[data-sync-room-name]");
    if (syncRoomNameInput) {
      state.syncRoomName = `${syncRoomNameInput.value || ""}`.trimStart();
      return;
    }

    const syncRoomSelect = event.target.closest("[data-sync-room-select]");
    if (syncRoomSelect) {
      const roomId = `${syncRoomSelect.value || ""}`.trim();
      const room = getCloudSyncRoomById(roomId);
      if (!room) {
        const previousRoomId = `${cloudSyncSession?.activeRoomId || ""}`.trim();
        stopCloudSyncLoop();
        if (previousRoomId) {
          persistWorkspaceSnapshot(previousRoomId);
        }
        cloudSyncSession = {
          rooms: getCloudSyncRooms(),
          activeRoomId: ""
        };
        saveCloudSyncSession();
        loadWorkspaceSnapshot("", { shouldRender: false });
        state.syncRoomId = "";
        state.syncRoomName = "";
        state.syncPin = "";
        state.syncPassword = "";
        state.syncConnected = false;
        setCloudSyncStatus("No active playgroup selected.");
        return;
      }
      const activeRoom = room;
      state.syncRoomId = activeRoom.id;
      state.syncRoomName = activeRoom.name;
      state.syncPin = activeRoom.pin;
      state.syncPassword = activeRoom.password || "";
      state.syncConnected = true;
      startCloudSyncLoop(activeRoom, { syncNow: true, silent: true });
      setCloudSyncStatus(`Connected to ${activeRoom.name}.`);
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
      renderSearchResults(seat, [], query);
      if (`${query}`.trim().length < 2) return;
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
  if (reason === "Pass") {
    triggerHaptic("step");
  }
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
    if (isSingleSeatProfileEditorMode()) {
      div.classList.add("single-seat-editor");
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
      dragHoverTargetIndex = index;

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
      triggerHaptic("tap");
      renderStartSetupScreen();
    });

    div.addEventListener("pointerup", (e) => {
      if (!isDragging) return;


      isDragging = false;
      dragStartIndex = null;
      dragHoverTargetIndex = null;
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
  const hoveredTargetIndex = targetPlayer
    ? parseInt(targetPlayer.id.replace("player", ""), 10)
    : null;

  document.querySelectorAll(".player").forEach(p =>
    p.classList.remove("target-highlight")
  );

  if (targetPlayer) {
    targetPlayer.classList.add("target-highlight");
  }

  if (hoveredTargetIndex !== dragHoverTargetIndex) {
    const enteredNewOtherPlayer =
      Number.isInteger(hoveredTargetIndex) &&
      hoveredTargetIndex !== dragStartIndex;
    dragHoverTargetIndex = hoveredTargetIndex;
    if (enteredNewOtherPlayer) {
      triggerHaptic("minimal");
    }
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

  if (count === 1) {
    game.style.gridTemplateColumns = "1fr";
    game.style.gridTemplateRows = "1fr";
    transformPlayer(0, 0, 100);
  }

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
    triggerHaptic("minimal");
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

  triggerHaptic("minimal");
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
  const forceAnchorSide = (anchor, side = "right") => {
    const normalizedSide = side === "left" ? "left" : "right";
    if (`${anchor || ""}`.startsWith("top-rail")) {
      return normalizedSide === "left" ? "top-rail-left" : "top-rail-right";
    }
    if (`${anchor || ""}`.startsWith("bottom-")) {
      return normalizedSide === "left" ? "bottom-left" : "bottom-right";
    }
    return normalizedSide === "left" ? "top-left" : "top-right";
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
    const overlayEditBtn = playerEl?.querySelector(".setup-edit-btn");
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
      if (overlayEditBtn) overlayEditBtn.dataset.anchor = poisonEl.dataset.anchor;
      if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = poisonEl.dataset.anchor;
      if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = poisonEl.dataset.anchor;
      if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = poisonEl.dataset.anchor;

      const shouldFlipSetupControls =
        ((selectedPlayerCount === 4 || selectedPlayerCount === 3) && (seatPos === 0 || seatPos === 1));

      if (shouldFlipSetupControls) {
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = flipHorizontalAnchor(overlayBackBtn.dataset.anchor);
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = flipHorizontalAnchor(overlayCancelBtn.dataset.anchor);
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = flipHorizontalAnchor(overlayEditBtn.dataset.anchor);
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
        overlayEditBtn?.dataset.anchor ||
        poisonEl.dataset.anchor;

      const isSingleSeatEditor = playerEl.classList.contains("single-seat-editor");
      if (isSingleSeatEditor) {
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = "top-right";
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = "top-right";
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = "top-right";
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = "top-right";
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = "top-left";
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = "top-left";
        if (commanderEl) commanderEl.dataset.anchor = "top-left";
        if (poisonEl) poisonEl.dataset.anchor = "top-right";
        setupRailAnchor = "top-right";
      }

      const shouldMirrorLeftRailSeat =
        !isSingleSeatEditor &&
        playerEl.dataset.setupRailSide === "left";
      if (shouldMirrorLeftRailSeat) {
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = forceAnchorSide(overlayEditBtn.dataset.anchor, "left");
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = forceAnchorSide(overlayPlusBtn.dataset.anchor, "left");
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = forceAnchorSide(overlayMinusBtn.dataset.anchor, "left");
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = forceAnchorSide(overlayBorrowBtn.dataset.anchor, "left");
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = forceAnchorSide(overlayBackBtn.dataset.anchor, "right");
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = forceAnchorSide(overlayCancelBtn.dataset.anchor, "right");
        setupRailAnchor =
          overlayBorrowBtn?.dataset.anchor ||
          overlayMinusBtn?.dataset.anchor ||
          overlayPlusBtn?.dataset.anchor ||
          overlayEditBtn?.dataset.anchor ||
          setupRailAnchor;
      }

      const shouldOpposeBackArrowRail =
        selectedPlayerCount === 2 ||
        (selectedPlayerCount === 3 && playerEl.classList.contains("seat-special-3"));

      if (shouldOpposeBackArrowRail) {
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = toTopRailAnchor(overlayEditBtn.dataset.anchor);
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = toTopRailAnchor(overlayPlusBtn.dataset.anchor);
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = toTopRailAnchor(overlayMinusBtn.dataset.anchor);
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = toTopRailAnchor(overlayBorrowBtn.dataset.anchor);
        setupRailAnchor =
          overlayBorrowBtn?.dataset.anchor ||
          overlayMinusBtn?.dataset.anchor ||
          overlayPlusBtn?.dataset.anchor ||
          overlayEditBtn?.dataset.anchor ||
          setupRailAnchor;
      }

      if (shouldOpposeBackArrowRail && overlayBackBtn && setupRailAnchor) {
        overlayBackBtn.dataset.anchor = flipHorizontalAnchor(setupRailAnchor);
      }

      const shouldFlipMirroredSetupSeat =
        (selectedPlayerCount === 2 && seatPos === 0)
        || (selectedPlayerCount === 3 && (seatPos === 0 || seatPos === 1));
      if (shouldFlipMirroredSetupSeat) {
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = flipHorizontalAnchor(overlayEditBtn.dataset.anchor);
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = flipHorizontalAnchor(overlayPlusBtn.dataset.anchor);
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = flipHorizontalAnchor(overlayMinusBtn.dataset.anchor);
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = flipHorizontalAnchor(overlayBorrowBtn.dataset.anchor);
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = flipHorizontalAnchor(overlayBackBtn.dataset.anchor);
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = flipHorizontalAnchor(overlayCancelBtn.dataset.anchor);
        setupRailAnchor =
          overlayBorrowBtn?.dataset.anchor ||
          overlayMinusBtn?.dataset.anchor ||
          overlayPlusBtn?.dataset.anchor ||
          overlayEditBtn?.dataset.anchor ||
          setupRailAnchor;
      }

      const shouldForceMirroredSeatClusters =
        (selectedPlayerCount === 2 && seatPos === 0)
        || (selectedPlayerCount === 3 && (seatPos === 0 || seatPos === 1));
      if (shouldForceMirroredSeatClusters) {
        const controlAnchor = shouldOpposeBackArrowRail ? "top-rail-left" : "bottom-left";
        const backAnchor = shouldOpposeBackArrowRail ? "top-rail-right" : "bottom-right";
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = controlAnchor;
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = controlAnchor;
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = controlAnchor;
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = controlAnchor;
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = backAnchor;
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = backAnchor;
        setupRailAnchor = controlAnchor;
      }

      const isBottomSpecialFive = selectedPlayerCount === 5 && seatPos === 4;
      if (isBottomSpecialFive) {
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = "top-rail-right";
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = "top-rail-right";
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = "top-rail-right";
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = "top-rail-right";
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = "top-left";
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = "top-left";
        setupRailAnchor = "top-rail-right";
      }

      if (!isSingleSeatEditor) {
        if (overlayBackBtn) overlayBackBtn.dataset.anchor = "top-left";
        if (overlayCancelBtn) overlayCancelBtn.dataset.anchor = "top-left";
        if (overlayEditBtn) overlayEditBtn.dataset.anchor = "top-rail-right";
        if (overlayPlusBtn) overlayPlusBtn.dataset.anchor = "top-rail-right";
        if (overlayMinusBtn) overlayMinusBtn.dataset.anchor = "top-rail-right";
        if (overlayBorrowBtn) overlayBorrowBtn.dataset.anchor = "top-rail-right";
        setupRailAnchor = "top-rail-right";
      }

      const resolvedSetupRailAnchor =
        overlayBorrowBtn?.dataset.anchor ||
        overlayMinusBtn?.dataset.anchor ||
        overlayPlusBtn?.dataset.anchor ||
        overlayEditBtn?.dataset.anchor ||
        setupRailAnchor;
      playerEl.dataset.setupRailSide = `${resolvedSetupRailAnchor || ""}`.endsWith("left") ? "left" : "right";
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
  recordPersistentStatsForEntry(entry);
  saveMatchHistory();
  syncActiveCloudRoom({ silent: true });
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

function getTopScoreName(scoreMap) {
  let topName = "";
  let topScore = -1;
  scoreMap.forEach((score, name) => {
    if (score > topScore) {
      topScore = score;
      topName = name;
    }
  });
  return topName;
}

function formatAverageTurnWin(turnValue) {
  if (!Number.isFinite(turnValue) || turnValue <= 0) return "-";
  const rounded = Math.round(turnValue * 10) / 10;
  return `Turn ${Number.isInteger(rounded) ? rounded : rounded.toFixed(1)}`;
}

function formatAverageDuration(secondsValue) {
  if (!Number.isFinite(secondsValue) || secondsValue <= 0) return "-";
  return formatTime(Math.round(secondsValue));
}

function getMostUsedCommanderBackgroundForProfile(profileName, decks = []) {
  const normalizedProfileName = normalizeLibraryName(profileName);
  if (!normalizedProfileName) return "";

  const commanderUsage = new Map();
  matchHistory.forEach((entry) => {
    const playersInEntry = Array.isArray(entry?.players) ? entry.players : [];
    playersInEntry.forEach((player) => {
      if (normalizeLibraryName(player?.name) !== normalizedProfileName) return;
      const commanderName = `${player?.commander || ""}`.trim();
      const commanderImage = `${player?.image || ""}`.trim();
      if (!commanderName && !commanderImage) return;
      const usageKey = normalizeLibraryName(commanderName) || commanderImage;
      if (!usageKey) return;
      const existing = commanderUsage.get(usageKey) || {
        count: 0,
        commanderName,
        image: commanderImage
      };
      existing.count += 1;
      if (!existing.image && commanderImage) {
        existing.image = commanderImage;
      }
      if (!existing.commanderName && commanderName) {
        existing.commanderName = commanderName;
      }
      commanderUsage.set(usageKey, existing);
    });
  });

  const mostUsed = Array.from(commanderUsage.values())
    .sort((a, b) => b.count - a.count)[0] || null;
  if (!mostUsed) return "";

  const matchingDeck = (Array.isArray(decks) ? decks : []).find((deck) =>
    normalizeLibraryName(deck?.cardName) === normalizeLibraryName(mostUsed.commanderName)
  );
  return `${matchingDeck?.image || mostUsed.image || ""}`.trim();
}

function getSingleSeatEditorBackgroundImage(state, seatIndex) {
  const seat = state?.seats?.[seatIndex] || getDefaultSeatState(seatIndex);
  const hasProfile = !!(`${seat?.profileId || ""}`.trim() && `${seat?.profileName || ""}`.trim());
  if (!hasProfile) return `${seat?.image || ""}`.trim();

  const profileDecks = getDecksForProfile(seat.profileId);
  if (seat.isEditingDeck) {
    const editingDeck = profileDecks.find((deck) => deck.id === seat.editingDeckId) || null;
    return `${editingDeck?.image || seat?.image || ""}`.trim();
  }

  const mostUsedCommanderImage = getMostUsedCommanderBackgroundForProfile(seat.profileName, profileDecks);
  if (mostUsedCommanderImage) return mostUsedCommanderImage;
  return `${profileDecks[0]?.image || seat?.image || ""}`.trim();
}

function getHistoryWinnerPanelImage(entry) {
  const playersInEntry = Array.isArray(entry?.players) ? entry.players : [];
  const winnerPlayer = Number.isInteger(entry?.winnerIndex) && entry.winnerIndex >= 0
    ? playersInEntry[entry.winnerIndex] || null
    : playersInEntry.find(player => player?.isWinner) || null;
  const image = `${winnerPlayer?.image || ""}`.trim();
  return image || DEFAULT_PLAYER_BACKGROUND;
}

function renderHistorySeatShell(contentMarkup, entry) {
  const image = getHistoryWinnerPanelImage(entry).replace(/"/g, "&quot;");
  return `
    <div class="history-seat-shell player single-seat-editor setup-seat-player setup-seat-outlined" id="player0" data-seat-pos="0" data-setup-rail-side="right" style="--seat-rot: 0deg; --heal-rise-x: 0.00%; --heal-rise-y: -150.00%;">
      <div class="bg" style="background-image: url(&quot;${image}&quot;); --rot: 0deg; width: 100%; height: 100%;"></div>
      <div class="commander-corner" data-anchor="top-left"></div>
      <div class="poison-corner is-empty" style="--seat-rot:0deg" data-anchor="top-right">
        <img src="./icons/Poison.svg" class="poison-icon icon-img" alt="">
        <span class="poison">0</span>
      </div>
      <div class="info_container" style="transform: rotate(0deg); transform-origin: center center;">
        <div class="setup-seat-overlay">
          ${contentMarkup}
        </div>
      </div>
    </div>
  `;
}

function buildMatchSummaryStats() {
  const globalStats = normalizePersistentGlobalStats(persistentStats?.global);
  return {
    numberOfMatches: globalStats.numberOfMatches,
    totalPlayTime: globalStats.totalPlayTime,
    averageGameTime: globalStats.numberOfMatches > 0
      ? (globalStats.totalPlayTime / globalStats.numberOfMatches)
      : null,
    averageTurnTime: globalStats.totalTurns > 0
      ? (globalStats.totalPlayTime / globalStats.totalTurns)
      : null,
    averageTurnWin: globalStats.numberOfWins > 0
      ? (globalStats.totalWinTurns / globalStats.numberOfWins)
      : null
  };
}

function buildProfileHistoryStats(profileName) {
  const normalizedProfileName = normalizeLibraryName(profileName);
  if (!normalizedProfileName) {
    return {
      numberOfMatches: 0,
      totalPlayTime: 0,
      numberOfWins: 0,
      averageTurnTime: null,
      averageTurnWin: null,
      totalDamage: 0,
      totalHealing: 0,
      enemy: "",
      targetOf: ""
    };
  }
  const profileStats = normalizePersistentProfileStats(
    persistentStats?.profiles?.[normalizedProfileName],
    profileName
  );

  return {
    numberOfMatches: profileStats.numberOfMatches,
    totalPlayTime: profileStats.totalPlayTime,
    numberOfWins: profileStats.numberOfWins,
    averageTurnTime: profileStats.totalTurns > 0 ? (profileStats.totalPlayTime / profileStats.totalTurns) : null,
    averageTurnWin: profileStats.numberOfWins > 0 ? (profileStats.totalWinTurns / profileStats.numberOfWins) : null,
    totalDamage: profileStats.totalDamage,
    totalHealing: profileStats.totalHealing,
    enemy: getTopScoreName(new Map(Object.entries(profileStats.enemyScores || {}))),
    targetOf: getTopScoreName(new Map(Object.entries(profileStats.targetScores || {})))
  };
}

function renderStatsSummaryGrid(items, extraClass = "") {
  return `
    <div class="stats-summary-grid ${extraClass}">
      ${items.map((item) => `
        <div class="stats-summary-card">
          <span>${escapeHtml(item.label)}</span>
          <strong>${escapeHtml(item.value)}</strong>
        </div>
      `).join("")}
    </div>
  `;
}

function renderHistoryDuelSeriesDetail(group) {
  const entries = Array.isArray(group?.entries) ? group.entries : [];
  const latestEntry = group?.latestEntry || entries[entries.length - 1];
  if (!latestEntry) return "";
  const duelBestOfChip = latestEntry?.mode === "magic"
    ? ` <span class="history-series-chip">Bo${normalizeDuelMatchLength(latestEntry.duelMatchLength)}</span>`
    : "";

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

  return renderHistorySeatShell(`
    <div class="history-detail-panel">
      <div class="history-topbar">
        <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history-detail" aria-label="Back">
          ${getIconMarkup("Back", "setup-back-icon")}
        </button>
        <h2>Game History</h2>
        <div class="history-topbar-spacer" aria-hidden="true"></div>
      </div>
      <div class="history-detail-shell">
        <div class="history-summary-copy history-summary-copy-detail">
          <div class="history-summary-names">${latestEntry.players.map(player => escapeHtml(player.name)).join(" | ")}${duelBestOfChip}</div>
          <div class="history-summary-date">${escapeHtml(formatHistoryDateTime(latestEntry.endedAt))}</div>
        </div>
        <div class="history-series-score">${wins[0]} - ${wins[1]}</div>
        <div class="history-series-list">
          ${gameRows}
        </div>
      </div>
    </div>
  `, latestEntry);
}

function renderHistoryEntryDetail(entry) {
  if (!entry) return "";
  const duelBestOfChip = entry?.mode === "magic"
    ? ` <span class="history-series-chip">Bo${normalizeDuelMatchLength(entry.duelMatchLength)}</span>`
    : "";
  return renderHistorySeatShell(`
    <div class="history-detail-panel">
      <div class="history-topbar">
        <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history-detail" aria-label="Back">
          ${getIconMarkup("Back", "setup-back-icon")}
        </button>
        <h2>Game History</h2>
        <div class="history-topbar-spacer" aria-hidden="true"></div>
      </div>
      <div class="history-detail-shell">
        <div class="history-summary-copy history-summary-copy-detail">
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
  `, entry);
}

function renderStartHistoryScreen() {
  const state = ensureSetupState();
  const groups = buildHistoryGroups();
  const summaryStats = buildMatchSummaryStats();
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

  return renderHistorySeatShell(`
    <div class="history-list-panel">
      <div class="history-topbar">
        <button class="setup-icon-circle-btn history-back-btn" data-action="back-from-history" aria-label="Back" ${state.historyDeleteMode ? "disabled" : ""}>
          ${getIconMarkup("Back", "setup-back-icon")}
        </button>
        <h2>${state.historyDeleteMode ? "Delete Games" : "Game History"}</h2>
        <button class="setup-icon-circle-btn history-delete-btn ${state.historyDeleteMode ? "active" : ""}" data-action="${state.historyDeleteMode ? "close-history-delete" : "open-history-delete"}" aria-label="Delete log mode">${getIconMarkup("Delete", "setup-inline-icon")}</button>
      </div>
      ${renderStatsSummaryGrid([
        { label: "Number of Matches", value: String(summaryStats.numberOfMatches) },
        { label: "Total Play Time", value: formatTime(summaryStats.totalPlayTime) },
        { label: "Average Game Time", value: formatAverageDuration(summaryStats.averageGameTime) },
        { label: "Average Turn Time", value: formatAverageDuration(summaryStats.averageTurnTime) },
        { label: "Average Turn Win", value: formatAverageTurnWin(summaryStats.averageTurnWin) }
      ], "history-top-stats")}
      <div class="history-list">
        ${entriesMarkup}
      </div>
    </div>
  `, selectedGroup?.type === "duel-series" ? selectedGroup.latestEntry : (groups[0]?.type === "duel-series" ? groups[0].latestEntry : groups[0]?.entry));
}

function renderStartHistoryStep() {
  const entriesMarkup = matchHistory.length
    ? matchHistory.map(entry => {
      const duelBestOfChip = entry?.mode === "magic"
        ? ` <span class="history-series-chip">Bo${normalizeDuelMatchLength(entry.duelMatchLength)}</span>`
        : "";
      return `
      <details class="history-entry">
        <summary class="history-entry-summary">
          <div class="history-summary-copy">
            <div class="history-summary-names">${entry.players.map(player => escapeHtml(player.name)).join(" · ")}${duelBestOfChip}</div>
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
    `;
    }).join("")
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
  triggerHaptic("minimal");

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
          <button class="sign-element" onclick="changeDamage(-1)" aria-label="Decrease damage">${getIconMarkup("Minus", "setup-inline-icon setup-minus-icon")}</button>
          <span id="damage-value">0</span>
          <button class="sign-element" onclick="changeDamage(1)" aria-label="Increase damage">${getIconMarkup("Plus", "setup-inline-icon setup-plus-icon")}</button>
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

  }, 80);

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
  triggerHaptic("minimal");
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
      triggerHaptic("minimal");
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
  triggerHaptic("minimal");
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

function closeDamageMode({ skipRender = false } = {}) {
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
  if (!skipRender) {
    render();
  }
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

  const didEndGame = checkGameEnd();
  closeDamageMode({ skipRender: didEndGame });
  if (!didEndGame) {
    autoPassIfActivePlayerDead();
  }
  cleanupDamageArrow();
  triggerHaptic("impact");
}

function cancelDamage() {
  damageSourceIndex = null;
  damageTargetIndex = null;
  pauseBtn.classList.remove("hidden");
  closeDamageMode();
  triggerHaptic("minimal");
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

  let highlightsPanel = document.getElementById("game-log-highlights-panel");
  if (!highlightsPanel) {
    highlightsPanel = document.createElement("div");
    highlightsPanel.id = "game-log-highlights-panel";
    highlightsPanel.className = "hidden";
    highlightsPanel.innerHTML = `<div id="game-log-highlights" class="game-log-highlights"></div>`;
    startScreen.appendChild(highlightsPanel);
  }

  let panel = document.getElementById("game-log-panel");
  if (!panel) {
    panel = document.createElement("div");
    panel.id = "game-log-panel";
    panel.className = "hidden";
    panel.innerHTML = `
      <div id="game-log-list" class="game-log-list"></div>
    `;
    startScreen.appendChild(panel);
  }

  return panel;
}

function renderGameLogPanel() {
  const panel = ensureGameLogPanel();
  if (!panel) return;

  syncActivePlayerTimer();
  const highlights = document.getElementById("game-log-highlights");
  const list = panel.querySelector("#game-log-list");
  if (!list || !highlights) return;
  renderGameLogHighlights(highlights);
  renderGameLogIntoList(list);
  bindDragScroll(list);
}

function closeGameLogPanel() {
  const panel = document.getElementById("game-log-panel");
  const highlightsPanel = document.getElementById("game-log-highlights-panel");
  if (!panel) return;
  panel.classList.add("hidden");
  if (highlightsPanel) highlightsPanel.classList.add("hidden");
}

function toggleGameLogPanel() {
  const panel = ensureGameLogPanel();
  const highlightsPanel = document.getElementById("game-log-highlights-panel");
  if (!panel) return;
  renderGameLogPanel();
  const willShow = panel.classList.contains("hidden");
  panel.classList.toggle("hidden", !willShow);
  if (highlightsPanel) highlightsPanel.classList.toggle("hidden", !willShow);
  triggerHaptic("minimal");
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

function getCurrentGameLogHighlights() {
  const livePlayers = players.slice(0, selectedPlayerCount);
  const liveStats = matchStats.slice(0, selectedPlayerCount);
  const totalGameTime = livePlayers.reduce((sum, player) => sum + (player?.totalTime || 0), 0);

  let mainEnemyName = " - ";
  let mostDamage = 0;
  let mostCommanderDamageName = " - ";
  let mostCommanderDamage = 0;
  let mostHealName = " - ";
  let mostHealValue = 0;

  liveStats.forEach((stats, index) => {
    const playerName = getPlayerNameForLog(livePlayers[index], index);
    const damageDealt = Number.isFinite(stats?.damageDealt) ? stats.damageDealt : 0;
    const commanderDamageDealt = Number.isFinite(stats?.commanderDamageDealt) ? stats.commanderDamageDealt : 0;
    const healingDone = Number.isFinite(stats?.healingDone) ? stats.healingDone : 0;

    if (damageDealt > mostDamage) {
      mostDamage = damageDealt;
      mainEnemyName = playerName;
    }

    if (commanderDamageDealt > mostCommanderDamage) {
      mostCommanderDamage = commanderDamageDealt;
      mostCommanderDamageName = playerName;
    }

    if (healingDone > mostHealValue) {
      mostHealValue = healingDone;
      mostHealName = playerName;
    }
  });

  if (mostDamage <= 0) {
    mainEnemyName = " - ";
  }

  if (mostCommanderDamage <= 0) {
    mostCommanderDamageName = " - ";
  }

  if (mostHealValue <= 0) {
    mostHealName = " - ";
  }

  return [
    { label: "Total Time", value: `${formatTime(totalGameTime)} (Turn ${turnNumber})` },
    { label: "Main Enemy", value: mainEnemyName === " - " ? " - " : `${mainEnemyName} (${mostDamage} damage)` },
    { label: "Most Commander Damage", value: mostCommanderDamageName === " - " ? " - " : `${mostCommanderDamageName} (Dealt ${mostCommanderDamage} damage)` },
    { label: "Most Heal", value: mostHealName === " - " ? " - " : `${mostHealName} (${mostHealValue} life gained)` }
  ];
}

function renderGameLogHighlights(container) {
  if (!container) return;

  const cards = getCurrentGameLogHighlights();
  container.innerHTML = renderStatsSummaryGrid(cards, "game-log-top-stats");
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
    menuBtn.classList.remove("hidden");
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
    triggerHaptic("minimal");
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
  triggerHaptic("minimal");

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
  pushUndoSnapshot();
  winnerIndex = null;
  lastEliminationCause = null;
  lastEliminationSelections = [];
  saveState();
  triggerHaptic("minimal");
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
  const projectedSeries = isDuelMode() ? getProjectedDuelSeriesState(winnerIndex) : null;
  const isFinalDuelScreen = isDuelMode() && isDuelSeriesCompleteForState(projectedSeries);
  const seriesWinnerIndex = isFinalDuelScreen ? getDuelSeriesWinnerIndex(projectedSeries) : null;
  const hasWinner = winnerIndex !== undefined && winnerIndex !== null && winnerIndex >= 0;
  const displayWinnerIndex = Number.isInteger(seriesWinnerIndex)
    ? seriesWinnerIndex
    : (hasWinner ? winnerIndex : null);
  const hasDisplayWinner = Number.isInteger(displayWinnerIndex) && displayWinnerIndex >= 0;

  // In duel, keep the game winner visually active on the board.
  if (isDuelMode() && hasWinner) {
    activePlayerIndex = winnerIndex;
    render();
  }

  applySeriesWinnerSeatHighlight(isFinalDuelScreen ? seriesWinnerIndex : null);

  // Show end screen
  const endScreen = document.getElementById("end-screen");
  endScreen.classList.toggle("no-winner", !hasDisplayWinner);
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
    hasDisplayWinner
      ? players[displayWinnerIndex].name
      : "No Winner";

  const endBg = document.getElementById("end-screen-bg");
  if (endBg) {
    if (isDuelMode() || isFinalDuelScreen) {
      endBg.style.backgroundImage = "none";
    } else {
      const bgPlayerIndex = hasDisplayWinner ? displayWinnerIndex : null;
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
persistentStats = loadPersistentStats();
syncTombstones = loadSyncTombstones();
applySyncTombstonesToLocalData();
syncPersistentStatsFromHistory();
resumeSessions = loadResumeSessions();
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
  const activeRoom = getActiveCloudSyncRoom();
  if (activeRoom) {
    if (cloudSyncPending) {
      syncActiveCloudRoom({ silent: true });
    } else {
      startCloudSyncLoop(activeRoom, { syncNow: true, silent: true });
    }
  }
});

const hasLoadedState = loadState();
if (!hasLoadedState) {
  hasStartedGame = false;
  selectedPlayerCount = 0;
  isPaused = true;
  resetSetupState();
}

const initialCloudSyncRoom = getActiveCloudSyncRoom();
if (initialCloudSyncRoom) {
  startCloudSyncLoop(initialCloudSyncRoom, { syncNow: true, silent: true });
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

    if (handleDeviceBackNavigation()) {
      window.history.pushState({ lifexExitGuard: true }, "", window.location.href);
      return;
    }

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

function isVisibleActionButton(btn) {
  return !!btn && !btn.disabled && btn.getClientRects().length > 0;
}

function triggerVisibleAction(action) {
  const btn = document.querySelector(`button[data-action="${action}"]`);
  if (!isVisibleActionButton(btn)) return false;
  btn.click();
  return true;
}

function handleDeviceBackNavigation() {
  const state = ensureSetupState();

  if (state.qrOpen) {
    if (state.qrView === "share" && state.qrCloseOnShareExit) {
      return triggerVisibleAction("close-qr");
    }
    if (state.qrView === "share" || state.qrView === "scan") {
      return triggerVisibleAction("back-qr-menu") || triggerVisibleAction("close-qr");
    }
    return triggerVisibleAction("close-qr");
  }

  if (state.step === "history") {
    if (state.historyDeleteMode) {
      return triggerVisibleAction("close-history-delete");
    }
    if (state.historyView === "detail") {
      return triggerVisibleAction("back-from-history-detail");
    }
    return triggerVisibleAction("back-from-history");
  }

  if (isProfileEditorMode(state)) {
    if (state.step === "seats") {
      const seatStates = Array.isArray(state.seats) ? state.seats : [];
      const hasAnyDeckDeletion = seatStates.some(seat => seat?.isDeletingDeck);
      const hasAnyProfileDeletion = seatStates.some(seat => seat?.isDeletingProfile);
      const hasAnyDeckArtEdit = seatStates.some(seat => seat?.isEditingDeck && seat?.isEditingDeckArt);
      const hasAnyDeckEdit = seatStates.some(seat => seat?.isEditingDeck);
      const hasAnyDeckAdd = seatStates.some(seat => seat?.isAddingDeck);
      const hasAnyProfileEdit = seatStates.some(seat => seat?.isEditingProfile);
      const hasAnyProfileAdd = seatStates.some(seat => seat?.isAddingProfile);
      const hasAnySelectedProfile = seatStates.some(seat => `${seat?.profileId || ""}`.trim());

      if (hasAnyDeckDeletion) {
        return triggerVisibleAction("close-delete-deck");
      }
      if (hasAnyProfileDeletion) {
        return triggerVisibleAction("close-delete-profile");
      }
      if (hasAnyDeckArtEdit) {
        return triggerVisibleAction("close-edit-deck-art");
      }
      if (hasAnyDeckEdit) {
        return triggerVisibleAction("close-edit-deck");
      }
      if (hasAnyDeckAdd) {
        return triggerVisibleAction("close-add-deck");
      }
      if (hasAnyProfileEdit) {
        return triggerVisibleAction("close-edit-profile");
      }
      if (hasAnyProfileAdd) {
        return triggerVisibleAction("close-add-profile");
      }
      if (hasAnySelectedProfile) {
        return triggerVisibleAction("back-to-config");
      }

      const orderedActions = [
        "close-delete-deck",
        "close-delete-profile",
        "close-edit-deck-art",
        "close-edit-deck",
        "close-add-deck",
        "close-edit-profile",
        "close-add-profile",
        "go-back-profile-seat",
        "back-to-config"
      ];
      return orderedActions.some(action => triggerVisibleAction(action));
    }
    return triggerVisibleAction("back-to-config");
  }

  return false;
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


//window.addEventListener("contextmenu", (e) => e.preventDefault()); //PREVENT RIGHT CLICK

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

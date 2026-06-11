# LifeX

LifeX is a mobile-first Magic: The Gathering life counter for Commander pods and 1v1 games. It runs as a static PWA and can optionally sync playgroup data through a Cloudflare Worker Durable Object room.

The app is designed for table play: portrait-only layout, fast life changes, commander damage, poison, monarch tracking, game logs, profiles, decks, Scryfall art lookup, QR sharing, offline app shell caching, and cloud playgroup sync.

## Features

- Commander pod support for up to 6 players.
- 1v1 Magic mode with best-of match tracking.
- Life, poison, commander damage, healing, monarch, mill, wincon, combo, and combat/non-combat outcome tracking.
- Turn timer, undo stack, pause menu, end-game summary, and game log highlights.
- Local profile/deck library stored in `localStorage`.
- Scryfall integration for commander search, autocomplete, prints, and card art.
- Custom bundled commander art in `custom-art/`.
- QR-based transfer and cloud sync room joining.
- PWA support with installable fullscreen mode and offline app shell caching.
- Cloudflare Durable Object sync rooms with optional admin/debug maintenance URLs.

## Project Structure

```text
.
|-- app.js                   # Main client app
|-- style.css                # App styling
|-- index.html               # PWA entry point
|-- sw.js                    # Service worker and offline/image caching
|-- manifest.webmanifest     # PWA manifest
|-- worker.js                # Cloudflare Worker + Durable Object sync API
|-- wrangler.jsonc           # Cloudflare deployment config
|-- scripts/build-static.mjs # Copies static assets into dist/
|-- icons/                   # App and UI icons
|-- img/                     # Default backgrounds
|-- custom-art/              # Bundled custom commander art
|-- fonts/                   # Google Sans Code fonts
`-- vendor/                  # Third-party browser libraries
```

## Requirements

- Node.js
- npm
- Cloudflare Wrangler for Worker development/deploys

Wrangler is not listed as a project dependency, so use `npx wrangler ...` or install it globally.

## Local Development

Build the static bundle:

```bash
npm run build
```

Run through Cloudflare Worker dev mode:

```bash
npx wrangler dev
```

This serves the Worker API and the static assets from `dist/`, matching production behavior more closely than opening `index.html` directly.

## Deployment

Build first:

```bash
npm run build
```

Deploy to Cloudflare:

```bash
npx wrangler deploy
```

The Worker name is configured as `lifex` in `wrangler.jsonc`. Static assets are served from:

```text
./dist
```

The Durable Object binding is:

```text
SYNC_ROOM -> SyncRoom
```

## Environment Variables

Set this secret in Cloudflare for debug and admin maintenance routes:

```bash
npx wrangler secret put DEBUG_SYNC_SECRET
```

The same secret is used as the `key` query parameter for admin/debug URLs.

## Important URLs

Replace `BASE_URL` with your deployed app URL, for example:

```text
https://lifex.<your-workers-subdomain>.workers.dev
```

or your custom domain.

### App

```text
GET BASE_URL/
GET BASE_URL/index.html
GET BASE_URL/manifest.webmanifest
GET BASE_URL/sw.js
```

### Public Sync API

Create a new sync room with a 4-digit room password:

```text
POST BASE_URL/api/sync/create
```

Body:

```json
{ "password": "1234" }
```

Ensure or create a known 4-digit PIN room:

```text
POST BASE_URL/api/sync/1234/ensure
```

Body:

```json
{ "password": "5678" }
```

Sync local room data with the cloud room:

```text
POST BASE_URL/api/sync/1234/sync
```

Body:

```json
{
  "password": "5678",
  "bundle": {
    "profiles": [],
    "decks": [],
    "games": [],
    "historyEntries": [],
    "tombstones": { "profiles": [], "decks": [] },
    "stats": []
  }
}
```

Reset match data for a room while keeping profiles/decks:

```text
POST BASE_URL/api/sync/1234/reset-match-data
```

Body:

```json
{ "password": "5678" }
```

This clears cloud `games`, `historyEntries`, and device stats for that room, while preserving profiles, decks, tombstones, PIN, and password.

## Admin And Reset URLs

All admin URLs require:

```text
?key=DEBUG_SYNC_SECRET
```

Use the actual secret value, not the literal variable name.

Debug one room:

```text
GET BASE_URL/api/sync/1234/debug?key=YOUR_SECRET
```

Admin reset match data for one room:

```text
GET  BASE_URL/api/sync/1234/admin/reset-match-data?key=YOUR_SECRET
POST BASE_URL/api/sync/1234/admin/reset-match-data?key=YOUR_SECRET
```

Admin wipe one room entirely:

```text
GET  BASE_URL/api/sync/1234/admin/wipe?key=YOUR_SECRET
POST BASE_URL/api/sync/1234/admin/wipe?key=YOUR_SECRET
```

List indexed room PINs:

```text
GET BASE_URL/api/sync/admin/list-codes?key=YOUR_SECRET
```

Wipe every indexed room:

```text
GET  BASE_URL/api/sync/admin/wipe-all?key=YOUR_SECRET
POST BASE_URL/api/sync/admin/wipe-all?key=YOUR_SECRET
```

### Admin `curl` Examples

Reset one room's match data:

```bash
curl -X POST "BASE_URL/api/sync/1234/admin/reset-match-data?key=YOUR_SECRET"
```

Wipe one room:

```bash
curl -X POST "BASE_URL/api/sync/1234/admin/wipe?key=YOUR_SECRET"
```

List room codes:

```bash
curl "BASE_URL/api/sync/admin/list-codes?key=YOUR_SECRET"
```

Wipe all indexed rooms:

```bash
curl -X POST "BASE_URL/api/sync/admin/wipe-all?key=YOUR_SECRET"
```

## Data Persistence

Client-side data is stored in browser `localStorage` under keys such as:

- `lifeTrackerState`
- `lifeTrackerProfilesV1`
- `lifeTrackerDecksV1`
- `lifeTrackerMatchHistoryV1`
- `lifeTrackerPersistentStatsV1`
- `lifeTrackerResumeSessionsV1`
- `lifeXCloudSyncV1`
- `lifeXSyncTombstonesV1`
- `lifeXRoomMatchResetV1`

Cloud sync room data is stored in the `SyncRoom` Durable Object. Room merge behavior preserves profiles/decks, merges tombstones, and only merges match data when it has not been superseded by a room match-data reset.

## Service Worker Notes

`sw.js` caches the app shell and bundled assets under:

```text
life-tracker-app-shell-v19
```

Remote commander images are cached separately under:

```text
life-tracker-commander-images-v1
```

The service worker keeps the app usable offline after the first successful load and caches up to 180 remote commander images.

## External APIs

LifeX uses Scryfall directly from the browser for card data and art:

```text
https://api.scryfall.com/cards/{id}
https://api.scryfall.com/cards/named?exact={name}
https://api.scryfall.com/cards/named?fuzzy={name}
https://api.scryfall.com/cards/autocomplete?q={query}
https://api.scryfall.com/cards/search?unique=prints&order=released&q={query}
```

## Notes For Future Maintenance

- Run `npm run build` before deploying so `dist/` contains the latest static files.
- Bump `APP_SHELL_CACHE` in `sw.js` when cached app-shell assets need a forced refresh.
- Treat admin wipe/reset URLs carefully. They are intentionally simple maintenance endpoints protected only by `DEBUG_SYNC_SECRET`.
- The public room password is a 4-digit numeric code; it is meant for playgroup convenience, not high-security access control.

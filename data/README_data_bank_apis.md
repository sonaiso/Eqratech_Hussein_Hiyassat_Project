# Data Bank API downloads

JSON files under `data/` are downloaded from the API links in **data_bank.csv** (column "رابط (API)").

## Folder structure (relative to `data/`)

| Folder | الباب (from data_bank) |
|--------|-------------------------|
| **01_phonology** | الهدف الأول : الفونولوجي (harakat, letters, word types, i3lal, phoneme meaning) |
| **02_mabniyat** | الهدف الثاني : باب المبنيات (pronouns, connectives effects, particles, building rules, i3rab types, etc.) |
| **connectives_api** | Connectives by category_id (أدوات الشرط، الاستدراك، الغائية، النفي، ...) |
| **03_juthur_mushtaqat** | الهدف الثالث : باب الجذر والمشتقات (shadda, quad verb, participles, marra, tamyeez, descriptive adjective) |
| **04_nahw** | الهدف الرابع : باب النحو (nominative, accusative, noun classification, comparative, exclamations, etc.) |

## How to refresh

Run from project root:

```bash
python3 scripts/download_data_bank_apis.py
```

- Successful responses are saved as `data/<folder>/<table_slug>.json`.
- Some endpoints return **404** (not implemented on server) or **429** (rate limit); the script skips them and reports at the end.
- A short delay between requests reduces 429; re-run later to retry failed URLs.

## Source

- **Index:** `data/data_bank.csv`
- **Script:** `scripts/download_data_bank_apis.py`

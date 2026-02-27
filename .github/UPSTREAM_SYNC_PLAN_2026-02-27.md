# Upstream Sync Plan (Staged)

Date: 2026-02-27
Source: origin/main (sonaiso/Eqratech_Hussein_Hiyassat_Project)
Target: upstream/main (salemqundil/Eqratech_Arabic_Diana_Project)

## Current Divergence
- upstream/main behind origin/main by 555 commits
- upstream/main ahead of origin/main by 0 commits
- changed files across range: 1261

## Recommendation
Do NOT do a single full-branch merge into upstream main.
Use staged sync PRs to reduce conflict risk and review load.

## Stage 1 (High value, low blast radius)
Cherry-pick and open PR with these commits only:
1. c800dd2  fix(core): recover C2a/C2b integrity and restore test-stable morphology pipeline
2. 97f176e  feat(web-api): align FastAPI routes and response contract with test expectations
3. 453c288  test: remove return-from-test anti-pattern in integration suites

Optional docs in same PR or separate docs-only PR:
4. db42aaf  docs(audit): add compact branch merge strategy log
5. f9dfeef  docs(sync): add compact upstream release notes for 2026-02-27

## Stage 2 (CI and reliability)
After Stage 1 is merged and green:
- sync PatternMatcher stabilization line (e9f88c7 and prerequisite fixes if needed)
- sync CI workflow updates in a dedicated PR
- run full test suite and security checks

## Stage 3 (Broader content sync)
Split by domain into independent PRs:
- morphology/phonology engines
- data and corpus assets
- docs and tutorials
- coq/proofs and theoretical modules

## Execution Commands (in upstream clone)
- git checkout main
- git pull origin main
- git checkout -b sync/stage1-core-web
- git remote add source https://github.com/sonaiso/Eqratech_Hussein_Hiyassat_Project.git  # if missing
- git fetch source
- git cherry-pick c800dd2
- git cherry-pick 97f176e
- git cherry-pick 453c288
- # optional docs commits:
- git cherry-pick db42aaf
- git cherry-pick f9dfeef
- python -m pytest -q
- git push origin sync/stage1-core-web
- open PR to upstream/main

## Risk Notes
- Full sync now is high risk due to scale (555 commits, 1261 files).
- Stage 1 is designed to deliver tested fixes quickly with manageable review scope.
- Keep each stage independently testable and revertible.

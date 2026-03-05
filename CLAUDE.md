# CLAUDE.md -- AdiabaticGrover

## Build Command

```bash
lake build AdiabaticGrover 2>&1 | tail -40
```

**NEVER run bare `lake build`** -- it rebuilds all of mathlib (~2 hours).

## Project Structure

- `AdiabaticGrover/` -- Lean 4 source files
- `HANDOFF.md` -- Mathematical analysis and implementation plan
- `AGENTS.md` -- Agent instructions (read after `HANDOFF.md`)

## Workflow

1. Read `HANDOFF.md` first
2. Read `AGENTS.md` second
3. Build after every step: `lake build AdiabaticGrover 2>&1 | tail -40`
4. Sorries with documented goal states = success

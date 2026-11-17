module

public import Initialize.Tactic.Attr.Basic

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.NotAnd.is.OrNotS |
| comm | Bool.OrNotS.is.NotAnd |
| mp | Bool.OrNotS.of.NotAnd |
| mpr | Bool.NotAnd.of.OrNotS |
-/
@[comm, mp, mpr]
public theorem Bool.NotAnd.is.OrNotS :
-- imply
  ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-10-26

module

public import Initialize.Tactic.Attr.Basic

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.Ne.is.NotEq |
| comm | Bool.NotEq.is.Ne |
| mp | Bool.NotEq.of.Ne |
| mpr | Bool.Ne.of.NotEq |
-/
@[comm, mp, mpr]
public theorem Bool.Ne.is.NotEq
  {a b : α} :
-- imply
  a ≠ b ↔ ¬a = b := by
-- proof
  constructor <;>
  ·
    intro h h_eq
    contradiction

public theorem Bool.NotEq.of.Ne
  {a b : α} (h : a ≠ b) : ¬a = b :=
  (Ne.is.NotEq).mp h

public theorem Bool.Ne.of.NotEq
  {a b : α} (h : ¬a = b) : a ≠ b :=
  (Ne.is.NotEq).mpr h


-- created on 2025-04-20

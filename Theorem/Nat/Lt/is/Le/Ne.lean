module

public import Initialize.Tactic.Attr.Basic

public section


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Lt.is.Le.Ne |
| comm | Nat.Le.Ne.is.Lt |
| mp | Nat.Le.Ne.of.Lt |
| mpr | Nat.Lt.of.Le.Ne |
-/
@[comm, mp, mpr]
public theorem Nat.Lt.is.Le.Ne
  [LinearOrder α]
  {a b : α} :
-- imply
  a < b ↔ a ≤ b ∧ a ≠ b := by
-- proof
  grind



public theorem Nat.Lt.of.Le.Ne
  [LinearOrder α]
  {a b : α}
  (h₀ : a ≤ b)
  (h₁ : a ≠ b) :
  a < b :=
  (Nat.Lt.is.Le.Ne).mpr ⟨h₀, h₁⟩

-- created on 2025-11-13
-- updated on 2026-10-26

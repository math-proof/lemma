import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.ModEq.is.Mod |
| comm | Nat.Mod.is.ModEq |
| mp | Nat.Mod.of.ModEq |
| mpr | Nat.ModEq.of.Mod |
-/
@[path, comm, mp, mpr]
private lemma main
-- given
  (m n d : ℕ) :
-- imply
  m ≡ n [MOD d] ↔ m % d = n % d := by
-- proof
  rfl


-- created on 2026-08-02

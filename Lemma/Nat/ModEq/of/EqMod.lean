import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.ModEq.of.EqMod |
| comm 1 | Nat.ModEq.of.Eq_Mod |
-/
@[main, comm 1]
private lemma main
  {d r r' : ℕ}
-- given
  (h : r % d = r') :
-- imply
  r ≡ r' [MOD d] := by
-- proof
  rw [Nat.ModEq, h]
  if h0 : d = 0 then
    simp [h0, Nat.mod_zero]
  else
    have hd : 0 < d := Nat.pos_of_ne_zero h0
    exact (Nat.mod_eq_of_lt (h ▸ Nat.mod_lt r hd)).symm


-- created on 2026-08-02

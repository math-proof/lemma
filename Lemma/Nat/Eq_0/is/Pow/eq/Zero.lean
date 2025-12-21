import sympy.Basic


/--
| attributes | lemma | comment|
| :---: | :---: | :---: |
| main | Nat.Eq_0.is.Pow.eq.Zero ||
| mp 12 | Nat.Pow.eq.Zero.of.Eq_0 |requires only [MonoidWithZero α] |
| mpr  | Nat.Eq_0.of.Pow.eq.Zero | [NoZeroDivisors α] [NeZero (1 : α)] are needed|
| mp.mt 12 | Nat.Ne_0.of.Pow.ne.Zero |requires only [MonoidWithZero α] |
| mpr.mt  | Nat.Pow.ne.Zero.of.Ne_0 | [NoZeroDivisors α] [NeZero (1 : α)] are needed|
-/
@[main, mp 12, mpr, mp.mt 12, mpr.mt]
private lemma main
  [NeZero (n : ℕ)]
  [MonoidWithZero α]
  [NoZeroDivisors α]
  [NeZero (1 : α)]
-- given
  (x : α) :
-- imply
  x = 0 ↔ x ^ n = 0 := by
-- proof
  constructor
  <;> intro h
  <;> have h_n := NeZero.ne n
  ·
    subst h
    simp_all
  ·
    contrapose! h
    induction n with
    | zero =>
      simp_all
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        simp_all
      else
        exact ⟨ih h_n, h⟩


-- created on 2025-12-20

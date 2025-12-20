import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Eq_0.is.Pow.eq.Zero |
| comm | Int.Pow.eq.Zero.is.Eq_0 |
| mp   | Int.Pow.eq.Zero.of.Eq_0 |
| mpr  | Int.Eq_0.of.Pow.eq.Zero |
| mp.mt | Int.Ne_0.of.Pow.ne.Zero |
| mpr.mt | Int.Pow.ne.Zero.of.Ne_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [NeZero (n : ℕ)]
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a : α) :
-- imply
  a = 0 ↔ a ^ n = 0 := by
-- proof
  have h_n := NeZero.ne n
  constructor <;>
    intro h
  .
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        simp_all
  .
    contrapose! h
    induction n with
    | zero =>
      contradiction
    | succ n ih =>
      simp [pow_succ]
      if h_n : n = 0 then
        subst h_n
        simp_all
      else
        have ih := ih h_n
        simp_all


-- created on 2025-12-20

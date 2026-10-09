import Mathlib
import sympy.Basic

open GenContFract

/--
[of_den_succ_lt_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/ContinuedFractions/Computation/Approximations.lean)
-/
@[main]
private lemma main
  [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
  {v : K} {n : ℕ}
-- given
  (not_terminatedAt : ¬(GenContFract.of v).TerminatedAt (n + 1)) :
-- imply
  (GenContFract.of v).dens (n + 1) < (GenContFract.of v).dens (n + 2) := by
-- proof
  let g := GenContFract.of v
  obtain ⟨gp, hgp⟩ : ∃ gp, g.s.get? (n + 1) = some gp :=
    Option.ne_none_iff_exists'.mp not_terminatedAt
  have ha : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a hgp)
  have hb : 1 ≤ gp.b := of_one_le_get?_partDen (partDen_eq_s_b hgp)
  have hn : n = 0 ∨ ¬g.TerminatedAt (n - 1) := by
    if hn0 : n = 0 then
      exact Or.inl hn0
    else
      exact Or.inr (mt (terminated_stable (by omega)) not_terminatedAt)
  have hdn : 0 < g.dens n := by
    refine lt_of_lt_of_le ?_ (succ_nth_fib_le_of_nth_den hn)
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hmono : g.dens (n + 1) ≤ gp.b * g.dens (n + 1) := by
    simpa using mul_le_mul_of_nonneg_right hb zero_le_of_den
  rw [dens_recurrence hgp rfl rfl, ha, one_mul]
  apply lt_of_le_of_lt hmono
  apply lt_add_of_pos_right _ hdn


-- created on 2026-10-09

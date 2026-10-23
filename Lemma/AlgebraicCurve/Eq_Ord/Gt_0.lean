import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Repartitions
import Lemma.Definitions.Def_AlgebraicCurve_IsCurveOver
import Lemma.P2M.Util

open AlgebraicCurve

/--
[AlgebraicCurve_exists_divisor_forall_eq_weightFloor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_exists_divisor_forall_eq_weightFloor.lean)
-/

private lemma  exists_divisor_ord (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [IsCurveOver K F] (f : F) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = v.ord f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, fun v => by simp⟩
  · have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    exact ⟨D, hD⟩
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
  {y : F}
  {m : ℕ} :
-- imply
  ∃ D : AlgebraicCurve.Divisor K F, ∀ w : AlgebraicCurve.Place K F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := by
-- proof
  classical
  obtain ⟨Dj, hDj⟩ := exists_divisor_ord K y
  obtain ⟨Dc, hDc⟩ := exists_divisor_ord K (y - 1728)

  let R : Place K F → ℤ := fun w =>
    (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
      + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
      + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0)
  have hsupp : ∀ w, R w ≠ 0 → w ∈ Dj.support ∪ Dc.support := by
    intro w hw
    by_contra hmem
    rw [Finset.mem_union, not_or, Finsupp.mem_support_iff, Finsupp.mem_support_iff, not_not, not_not,
      hDj w, hDc w] at hmem
    apply hw
    simp only [R, hmem.1, hmem.2, lt_irrefl, ite_false, add_zero]
  refine ⟨Finsupp.onFinset (Dj.support ∪ Dc.support) R hsupp, fun w => ?_⟩
  rw [Finsupp.onFinset_apply]


-- created on 2026-10-23

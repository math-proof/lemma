import Mathlib
import sympy.Basic

open scoped Pointwise

/--
[QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuotSMulTop_span_eq_top_of_span_quotientMk_eq_top.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [IsLocalRing R] [Module.Finite R M]
  {x : R}
  {m : ι → M}
-- given
  (hx : x ∈ IsLocalRing.maximalIdeal R)
  (hspan : Submodule.span (R ⧸ Ideal.span {x}) (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
-- imply
  Submodule.span R (Set.range m) = ⊤ := by
-- proof
  have h1 : Submodule.span R
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective,
      hspan, Submodule.restrictScalars_top]
  have h2 : (Submodule.span R (Set.range m)).map
      (Submodule.mkQ (x • ⊤ : Submodule R M)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h1
  rw [Submodule.map_mkQ_eq_top] at h2
  have hjac : Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
    le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac ?_)
  rw [Submodule.ideal_span_singleton_smul, sup_comm, h2]


-- created on 2026-10-05

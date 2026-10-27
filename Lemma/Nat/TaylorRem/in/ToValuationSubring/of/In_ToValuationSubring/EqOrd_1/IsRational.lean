import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.AlgebraicCurve_PlaceTaylorCoeff
import Lemma.Scheme.PlaceEvaluationAlgebra
import Lemma.AlgebraicCurve.Repartitions
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.Place

/--
[AlgebraicCurve_Place_taylorRem_mem_toValuationSubring](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_taylorRem_mem_toValuationSubring.lean)
-/

private lemma  evalAt_sub_of_mem'
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F) (hv : v.IsRational) {f g : F}
  (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
  v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

private lemma  ord_nonneg_of_mem'
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
  0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem hf)).resolve_left hf0

private lemma  sub_evalAt_mul_inv_mem'
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
  {g : F} (hg : g ∈ v.toValuationSubring) :
  (g - algebraMap K F (v.evalAt g)) * t⁻¹ ∈ v.toValuationSubring := by
  have hc : algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := v.algebraMap_mem' _
  have hx : g - algebraMap K F (v.evalAt g) ∈ v.toValuationSubring := sub_mem hg hc
  by_cases hx0 : g - algebraMap K F (v.evalAt g) = 0
  ·
    rw [hx0, zero_mul]
    exact zero_mem _
  have ht0 : t ≠ 0 := by rintro rfl; simp [Place.ord_zero] at ht
  have hval : v.evalAt (g - algebraMap K F (v.evalAt g)) = 0 := by
    rw [evalAt_sub_of_mem' v hv hg hc, v.evalAt_algebraMap_eq, sub_self]
  have hord0 : v.ord (g - algebraMap K F (v.evalAt g)) ≠ 0 := fun h0 =>
    v.evalAt_ne_zero_of_ord_eq_zero hv hx0 h0 hval
  have hord1 : 1 ≤ v.ord (g - algebraMap K F (v.evalAt g)) := by
    have := ord_nonneg_of_mem' v hx hx0; omega
  apply v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hx0 (inv_ne_zero ht0))
  rw [v.ord_mul hx0 (inv_ne_zero ht0), v.ord_inv, ht]
  omega
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {v : Place K F}
  {t : F}
  {f : F}
  {r : ℕ}
-- given
  (hv : v.IsRational)
  (ht : v.ord t = 1)
  (hf : f ∈ v.toValuationSubring) :
-- imply
  taylorRem v t f r ∈ v.toValuationSubring := by
-- proof
  induction r with
  | zero => simpa using hf
  | succ r ih =>
    rw [taylorRem_succ]
    exact sub_evalAt_mul_inv_mem' v hv ht ih


-- created on 2026-10-23

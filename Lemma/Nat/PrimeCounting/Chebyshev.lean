import Mathlib
import sympy.Basic
open scoped Asymptotics


namespace Chebyshev

/--
[primeCounting_sub_theta_div_log_isLittleO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
lemma primeCounting_sub_theta_div_log_isLittleO
  :
-- imply
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - Chebyshev.theta x / Real.log x)
    =o[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
-- proof
  have haux : (fun x : ℝ => x / Real.log x ^ 2)
    =o[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
    refine Asymptotics.isLittleO_iff_tendsto' (by simp) |>.mpr ?_
    refine Filter.Tendsto.congr' (f₁ := fun x : ℝ => (Real.log x)⁻¹) ?_
      Real.tendsto_log_atTop.inv_tendsto_atTop
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hxlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
    field
  exact Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO haux

end Chebyshev

namespace Chebyshev

/--
[primeCounting_isEquivalent_of_theta_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
lemma primeCounting_isEquivalent_of_theta_isEquivalent
-- given
  (h : Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :
-- imply
  (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x) := by
-- proof
  have hlog : (fun x : ℝ => Real.log x) ~[Filter.atTop] (fun x : ℝ => Real.log x) :=
    Asymptotics.IsEquivalent.refl
  have hdiv : (fun x : ℝ => Chebyshev.theta x / Real.log x)
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x) :=
    h.div hlog
  have hadd := Asymptotics.IsLittleO.add_isEquivalent
    primeCounting_sub_theta_div_log_isLittleO hdiv
  refine hadd.congr_left ?_
  exact Filter.Eventually.of_forall fun x => sub_add_cancel _ _

end Chebyshev

namespace Chebyshev

/--
[theta_isEquivalent_of_primeCounting_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
lemma theta_isEquivalent_of_primeCounting_isEquivalent
-- given
  (h : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[Filter.atTop] (fun x : ℝ => x / Real.log x)) :
-- imply
  Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x := by
-- proof
  have hlog : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≠ 0 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact ne_of_gt (Real.log_pos hx)
  have hlogequiv : (fun x : ℝ => Real.log x) ~[Filter.atTop]
    (fun x : ℝ => Real.log x) :=
    Asymptotics.IsEquivalent.refl
  have hcancel : (fun x : ℝ => x / Real.log x) * Real.log
    =ᶠ[Filter.atTop] (fun x : ℝ => x) := by
    filter_upwards [hlog] with x hx
    simp only [Pi.mul_apply]
    exact div_mul_cancel₀ _ hx
  have hpi : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x)
    ~[Filter.atTop] (fun x : ℝ => x) :=
    (h.mul hlogequiv).trans_eventuallyEq hcancel
  have herr : (fun x : ℝ => ((Nat.primeCounting ⌊x⌋₊ : ℝ)
    - Chebyshev.theta x / Real.log x) * Real.log x)
    =o[Filter.atTop] (fun x : ℝ => x) :=
    (primeCounting_sub_theta_div_log_isLittleO.mul_isBigO
      (Asymptotics.isBigO_refl _ _)).trans_eventuallyEq hcancel
  have hsub := hpi.sub_isLittleO herr
  refine Filter.EventuallyEq.trans_isEquivalent ?_ hsub
  filter_upwards [hlog] with x hx
  simp only [Pi.sub_apply]
  rw [sub_mul, div_mul_cancel₀ _ hx]
  abel

end Chebyshev

namespace Chebyshev

/--
[primeCounting_isEquivalent_iff_theta_isEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/Chebyshev.lean)
-/
@[path]
lemma primeCounting_isEquivalent_iff_theta_isEquivalent
  :
-- imply
  ((fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ))
    ~[Filter.atTop] (fun x : ℝ => x / Real.log x))
    ↔ (Chebyshev.theta ~[Filter.atTop] fun x : ℝ => x) :=
-- proof
  ⟨theta_isEquivalent_of_primeCounting_isEquivalent,
    primeCounting_isEquivalent_of_theta_isEquivalent⟩

end Chebyshev


-- created on 2026-10-20
-- updated on 2026-10-23

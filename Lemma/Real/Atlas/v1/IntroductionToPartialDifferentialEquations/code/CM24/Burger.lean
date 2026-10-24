import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM24.Burger
open Burger


namespace Burger

/--
[differentiable_along_char](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM24/Burger.lean)
-/
@[path]
lemma differentiable_along_char
  {u : ℝ → ℝ → ℝ}
  {γ₀ γ₁ : ℝ → ℝ}
-- given
  (hC1 : ContDiff ℝ 1 (Function.uncurry u))
  (hγ₀_diff : Differentiable ℝ γ₀)
  (hγ₁_diff : Differentiable ℝ γ₁) :
-- imply
  Differentiable ℝ (fun s => u (γ₀ s) (γ₁ s)) :=
-- proof
  hC1.differentiable_one.comp (hγ₀_diff.prodMk hγ₁_diff)

end Burger

namespace Burger

/--
[deriv_along_char_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM24/Burger.lean)
-/
@[path]
lemma deriv_along_char_eq_zero
  {u : ℝ → ℝ → ℝ}
  {γ₀ γ₁ : ℝ → ℝ}
  {s : ℝ}
-- given
  (hu : IsBurgerSolution u)
  (hchar : IsCharacteristicCurve u γ₀ γ₁)
  (hγ₀_diff : Differentiable ℝ γ₀)
  (hγ₁_diff : Differentiable ℝ γ₁) :
-- imply
  deriv (fun s => u (γ₀ s) (γ₁ s)) s = 0 := by
-- proof
  obtain ⟨hC1, hpde⟩ := hu
  obtain ⟨hγ₀_eq, hγ₁_eq⟩ := hchar
  set L := fderiv ℝ (Function.uncurry u) (γ₀ s, γ₁ s)
  have hfderiv : HasFDerivAt (Function.uncurry u) L (γ₀ s, γ₁ s) :=
    (hC1.differentiable_one.differentiableAt).hasFDerivAt
  have hd₀ : HasDerivAt γ₀ 1 s := by
    rw [← hγ₀_eq s]; exact (hγ₀_diff s).hasDerivAt
  have hd₁ : HasDerivAt γ₁ (u (γ₀ s) (γ₁ s)) s := by
    rw [← hγ₁_eq s]; exact (hγ₁_diff s).hasDerivAt
  have hprod : HasDerivAt (fun s => (γ₀ s, γ₁ s)) ((1 : ℝ), u (γ₀ s) (γ₁ s)) s :=
    hd₀.prodMk hd₁
  have hchain : HasDerivAt (Function.uncurry u ∘ fun s => (γ₀ s, γ₁ s))
    (L ((1 : ℝ), u (γ₀ s) (γ₁ s))) s :=
    hfderiv.comp_hasDerivAt s hprod
  have hderiv_val : deriv (fun s => u (γ₀ s) (γ₁ s)) s = L ((1 : ℝ), u (γ₀ s) (γ₁ s)) :=
    (hchain : HasDerivAt (fun s => u (γ₀ s) (γ₁ s)) _ s).deriv
  rw [hderiv_val]
  set c := u (γ₀ s) (γ₁ s)
  have hlin : L ((1 : ℝ), c) = L (1, 0) + c * L (0, 1) := by
    have : ((1 : ℝ), c) = (1 : ℝ) • ((1 : ℝ), (0 : ℝ)) + c • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, one_mul]
  rw [hlin]
  have hL10 : L (1, 0) = deriv (fun t' => u t' (γ₁ s)) (γ₀ s) := by
    have hd : HasDerivAt (fun t' => u t' (γ₁ s)) (L (1, 0)) (γ₀ s) := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert hfderiv.comp (γ₀ s) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (γ₀ s) (γ₁ s)) using 1
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    exact hd.deriv.symm
  have hL01 : L (0, 1) = deriv (fun x' => u (γ₀ s) x') (γ₁ s) := by
    have hd : HasDerivAt (fun x' => u (γ₀ s) x') (L (0, 1)) (γ₁ s) := by
      rw [hasDerivAt_iff_hasFDerivAt]
      convert hfderiv.comp (γ₁ s) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (γ₀ s) (γ₁ s)) using 1
      ext
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, smul_eq_mul]
    exact hd.deriv.symm
  rw [hL10, hL01]
  exact hpde (γ₀ s) (γ₁ s)

end Burger

namespace Burger

/--
[burger_constant_along_characteristics](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM24/Burger.lean)
-/
@[path]
lemma burger_constant_along_characteristics
  {u : ℝ → ℝ → ℝ}
  {γ₀ γ₁ : ℝ → ℝ}
  {s₁ s₂ : ℝ}
-- given
  (hu : IsBurgerSolution u)
  (hchar : IsCharacteristicCurve u γ₀ γ₁)
  (hγ₀_diff : Differentiable ℝ γ₀)
  (hγ₁_diff : Differentiable ℝ γ₁) :
-- imply
  u (γ₀ s₁) (γ₁ s₁) = u (γ₀ s₂) (γ₁ s₂) := by
-- proof
  have hdiff : Differentiable ℝ (fun s => u (γ₀ s) (γ₁ s)) :=
    differentiable_along_char u γ₀ γ₁ hu.1 hγ₀_diff hγ₁_diff
  have hzero : ∀ s, deriv (fun s => u (γ₀ s) (γ₁ s)) s = 0 :=
    fun s => deriv_along_char_eq_zero u γ₀ γ₁ hu hchar hγ₀_diff hγ₁_diff s
  exact is_const_of_deriv_eq_zero hdiff hzero s₁ s₂

end Burger


-- created on 2026-10-23

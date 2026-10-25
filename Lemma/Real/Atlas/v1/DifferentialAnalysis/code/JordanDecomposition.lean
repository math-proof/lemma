import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.JordanDecomposition.Part5
open ContinuousFunctions
open ContinuousLinearMap


namespace ContinuousFunctions

/--
[posPartCLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma posPartCLM_apply
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X} :
-- imply
  posPartCLM u f = posPartFn u f := by
-- proof
  show (posPartLinearMap u).mkContinuous ‖u‖ _ f = posPartFn u f
  rw [LinearMap.mkContinuous_apply]
  rfl

end ContinuousFunctions

namespace ContinuousFunctions

/--
[posPartCLM_positive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma posPartCLM_positive
  [MetricSpace X]
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ} :
-- imply
  IsPositiveFunctional (posPartCLM u) := by
-- proof
  intro f hf
  rw [posPartCLM_apply]
  unfold posPartFn
  have hpos : zeroAtInftyPosPart f = f := by
    ext x; simp [posPart_apply, max_eq_left (hf x)]
  have hneg : zeroAtInftyNegPart f = 0 := by
    ext x; simp [negPart_apply, max_eq_right (by linarith [hf x] : -f x ≤ 0)]
  rw [hpos, hneg, posPartSup_zero]
  linarith [posPartSup_nonneg u f hf]

end ContinuousFunctions

namespace ContinuousFunctions

/--
[posPartCLM_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma posPartCLM_ge
  [MetricSpace X]
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  u f ≤ posPartCLM u f := by
-- proof
  rw [posPartCLM_apply]
  unfold posPartFn
  have hpos : zeroAtInftyPosPart f = f := by
    ext x; simp [posPart_apply, max_eq_left (hf x)]
  have hneg : zeroAtInftyNegPart f = 0 := by
    ext x; simp [negPart_apply, max_eq_right (by linarith [hf x] : -f x ≤ 0)]
  rw [hpos, hneg, posPartSup_zero, sub_zero]
  exact le_csSup (posPartSet_bddAbove u f hf)
    ⟨f, hf, fun _ => le_refl _, rfl⟩

end ContinuousFunctions

namespace ContinuousFunctions

/--
[norm_posPartCLM_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma norm_posPartCLM_le
  [MetricSpace X]
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ} :
-- imply
  ‖posPartCLM u‖ ≤ ‖u‖ :=
-- proof
LinearMap.mkContinuous_norm_le (posPartLinearMap u) (norm_nonneg u) _

end ContinuousFunctions

namespace ContinuousFunctions

/--
[norm_negPart_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma norm_negPart_le
  [MetricSpace X]
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ} :
-- imply
  ‖posPartCLM u - u‖ ≤ ‖u‖ := by
-- proof
  apply opNorm_le_bound _ (norm_nonneg u)
  intro f
  rw [ContinuousLinearMap.sub_apply, posPartCLM_apply]
  unfold posPartFn
  rw [Real.norm_eq_abs]
  have hf_decomp : u f = u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f) := by
    have := decompose_pos_neg f
    conv_lhs => rw [this]
    rw [map_sub]
  rw [hf_decomp]
  have key : ∀ (g : C₀Map X), (∀ x, 0 ≤ g x) →
    posPartSup u g - u g = posPartSup (-u) g := by
    intro g hg
    unfold posPartSup
    have h_shift : sSup (posPartSet u g) - u g =
      sSup ((fun r => r - u g) '' posPartSet u g) := by
      have := Monotone.map_csSup_of_continuousAt (f := fun r => r - u g)
        ((continuous_id.sub continuous_const).continuousAt)
        (fun _ _ h => sub_le_sub_right h _)
        (posPartSet_nonempty u g hg)
        (posPartSet_bddAbove u g hg)
      exact this
    rw [h_shift]
    congr 1
    ext r; constructor
    · rintro ⟨s, ⟨h, hh0, hhg, rfl⟩, rfl⟩
      refine ⟨g - h, fun x => ?_, fun x => ?_, ?_⟩
      · show g x - h x ≥ 0; linarith [hhg x]
      · show g x - h x ≤ g x; linarith [hh0 x]
      · show u h - u g = (-u) (g - h)
        simp only [ContinuousLinearMap.neg_apply, map_sub]; ring
    · rintro ⟨k, hk0, hkg, rfl⟩
      refine ⟨u (g - k), ⟨g - k, fun x => ?_, fun x => ?_, rfl⟩, ?_⟩
      · show g x - k x ≥ 0; linarith [hkg x]
      · show g x - k x ≤ g x; linarith [hk0 x]
      · simp only [ContinuousLinearMap.neg_apply, map_sub]; ring
  have hkey1 := key (zeroAtInftyPosPart f) (posPart_nonneg f)
  have hkey2 := key (zeroAtInftyNegPart f) (negPart_nonneg f)
  show |posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) -
    (u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f))| ≤ ‖u‖ * ‖f‖
  rw [show posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) -
    (u (zeroAtInftyPosPart f) - u (zeroAtInftyNegPart f)) =
    (posPartSup u (zeroAtInftyPosPart f) - u (zeroAtInftyPosPart f)) -
    (posPartSup u (zeroAtInftyNegPart f) - u (zeroAtInftyNegPart f)) by ring]
  rw [hkey1, hkey2]
  calc |posPartSup (-u) (zeroAtInftyPosPart f) - posPartSup (-u) (zeroAtInftyNegPart f)|
    = ‖posPartFn (-u) f‖ := by unfold posPartFn; rw [Real.norm_eq_abs]
    _ ≤ ‖-u‖ * ‖f‖ := posPartFn_bound (-u) f
    _ = ‖u‖ * ‖f‖ := by congr 1; exact norm_neg u

end ContinuousFunctions

namespace ContinuousFunctions

/--
[dual_jordan_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
lemma dual_jordan_decomposition
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ} :
-- imply
  ∃ u_pos u_neg : C₀Map X →L[ℝ] ℝ, IsPositiveFunctional u_pos ∧ IsPositiveFunctional u_neg ∧ u = u_pos - u_neg ∧ ‖u_pos‖ ≤ ‖u‖ ∧ ‖u_neg‖ ≤ ‖u‖ := by
-- proof
  refine ⟨posPartCLM u, posPartCLM u - u,
    posPartCLM_positive u, ?_, ?_, norm_posPartCLM_le u, norm_negPart_le u⟩
  ·
    intro f hf
    simp only [ContinuousLinearMap.sub_apply]
    linarith [posPartCLM_ge u f hf]
  ·
    ext f
    simp only [ContinuousLinearMap.sub_apply]
    ring

end ContinuousFunctions

/--
[c0_eval_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma c0_eval_le_norm_eq
  [MetricSpace X]
  {f : C₀Map X}
  {x : X} :
-- imply
  |f x| ≤ ‖f‖ := by
-- proof
  apply ContinuousFunctions.c0_eval_le_norm f x

/--
[c0_norm_le_of_nonneg_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma c0_norm_le_of_nonneg_le_eq
  [MetricSpace X]
  {f g : C₀Map X}
-- given
  (hg0 : ∀ x, 0 ≤ g x)
  (hgf : ∀ x, g x ≤ f x) :
-- imply
  ‖g‖ ≤ ‖f‖ := by
-- proof
  apply ContinuousFunctions.c0_norm_le_of_nonneg_le f g hg0 hgf

/--
[posPartSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSet_nonempty_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  (posPartSet u f).Nonempty := by
-- proof
  apply ContinuousFunctions.posPartSet_nonempty u f hf

/--
[posPartSet_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSet_bddAbove_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
-- given
  (_hf : ∀ x, 0 ≤ f x) :
-- imply
  BddAbove (posPartSet u f) := by
-- proof
  apply ContinuousFunctions.posPartSet_bddAbove u f _hf

/--
[posPartSup_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_nonneg_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  0 ≤ posPartSup u f := by
-- proof
  apply ContinuousFunctions.posPartSup_nonneg u f hf

/--
[posPartSup_le_norm_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_le_norm_mul_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  posPartSup u f ≤ ‖u‖ * ‖f‖ := by
-- proof
  apply ContinuousFunctions.posPartSup_le_norm_mul u f hf

/--
[posPartSup_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_zero_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ} :
-- imply
  posPartSup u 0 = 0 := by
-- proof
  apply ContinuousFunctions.posPartSup_zero u

/--
[posPartSup_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_add_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f₁ f₂ : C₀Map X}
-- given
  (hf₁ : ∀ x, 0 ≤ f₁ x)
  (hf₂ : ∀ x, 0 ≤ f₂ x) :
-- imply
  posPartSup u (f₁ + f₂) = posPartSup u f₁ + posPartSup u f₂ := by
-- proof
  apply ContinuousFunctions.posPartSup_add u f₁ f₂ hf₁ hf₂

/--
[posPartSup_smul_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_smul_pos_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
  {c : ℝ}
-- given
  (hf : ∀ x, 0 ≤ f x)
  (hc : 0 < c) :
-- imply
  posPartSup u (c • f) = c * posPartSup u f := by
-- proof
  apply ContinuousFunctions.posPartSup_smul_pos u f hf c hc

/--
[posPartSup_smul_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_smul_nonneg_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
  {c : ℝ}
-- given
  (hf : ∀ x, 0 ≤ f x)
  (hc : 0 ≤ c) :
-- imply
  posPartSup u (c • f) = c * posPartSup u f := by
-- proof
  apply ContinuousFunctions.posPartSup_smul_nonneg u f hf c hc

/--
[posPartSup_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartSup_well_defined_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
-- given
  (f h₁ h₂ : C₀Map X)
  (hh₁ : ∀ x, 0 ≤ h₁ x)
  (hh₂ : ∀ x, 0 ≤ h₂ x)
  (hf : f = h₁ - h₂) :
-- imply
  posPartSup u (zeroAtInftyPosPart f) - posPartSup u (zeroAtInftyNegPart f) = posPartSup u h₁ - posPartSup u h₂ := by
-- proof
  apply ContinuousFunctions.posPartSup_well_defined u f h₁ h₂ hh₁ hh₂ hf

/--
[posPartFn_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartFn_add_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f g : C₀Map X} :
-- imply
  posPartFn u (f + g) = posPartFn u f + posPartFn u g := by
-- proof
  apply ContinuousFunctions.posPartFn_add u f g

/--
[posPartFn_smul_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartFn_smul_nonneg_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  posPartFn u (c • f) = c * posPartFn u f := by
-- proof
  apply ContinuousFunctions.posPartFn_smul_nonneg u f c hc

/--
[posPartFn_smul_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartFn_smul_neg_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
  {c : ℝ}
-- given
  (hc : c < 0) :
-- imply
  posPartFn u (c • f) = c * posPartFn u f := by
-- proof
  apply ContinuousFunctions.posPartFn_smul_neg u f c hc

/--
[posPartFn_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartFn_smul_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X}
  {c : ℝ} :
-- imply
  posPartFn u (c • f) = c * posPartFn u f := by
-- proof
  apply ContinuousFunctions.posPartFn_smul u f c

/--
[posPartFn_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/JordanDecomposition.lean)
-/
@[path]
private lemma posPartFn_bound_eq
  [MetricSpace X]
  {u : C₀Map X →L[ℝ] ℝ}
  {f : C₀Map X} :
-- imply
  ‖posPartFn u f‖ ≤ ‖u‖ * ‖f‖ := by
-- proof
  apply ContinuousFunctions.posPartFn_bound u f


-- created on 2026-10-23

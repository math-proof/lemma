import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
open Finset StatMech StatMech.Walls StatMech.Walls.VBG


/--
[vbg_exp_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_exp_add_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {f g : Ω → ℝ} :
-- imply
  vbg_exp μ (fun ω => f ω + g ω) = vbg_exp μ f + vbg_exp μ g := by
-- proof
  apply StatMech.Walls.VBG.vbg_exp_add μ f g

/--
[vbg_exp_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_exp_const_mul_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {c : ℝ}
  {f : Ω → ℝ} :
-- imply
  vbg_exp μ (fun ω => c * f ω) = c * vbg_exp μ f := by
-- proof
  apply StatMech.Walls.VBG.vbg_exp_const_mul μ c f

/--
[vbg_exp_reweight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_exp_reweight_eq
  [Fintype Ω]
  {μ w : Ω → ℝ}
  {c : ℝ}
  {f : Ω → ℝ} :
-- imply
  vbg_exp (fun ω => μ ω * w ω / c) f = (∑ ω, μ ω * w ω * f ω) / c := by
-- proof
  apply StatMech.Walls.VBG.vbg_exp_reweight μ w c f

/--
[vbg_expPlus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_expPlus_eq_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {f : Ω → ℝ} :
-- imply
  vbg_exp (vbg_condPlus μ Y) f = (∑ ω, μ ω * Y ω * f ω) / vbg_exp μ Y := by
-- proof
  apply StatMech.Walls.VBG.vbg_expPlus_eq μ X Y Z f

/--
[vbg_expMinus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_expMinus_eq_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {f : Ω → ℝ} :
-- imply
  vbg_exp (vbg_condMinus μ Y) f = (∑ ω, μ ω * (1 - Y ω) * f ω) / (1 - vbg_exp μ Y) := by
-- proof
  apply StatMech.Walls.VBG.vbg_expMinus_eq μ X Y Z f

/--
[vbg_prop1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_prop1_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
-- given
  (hY : ∀ ω, Y ω * Y ω = Y ω)
  (hp0 : 0 < vbg_exp μ Y)
  (hp1 : vbg_exp μ Y < 1) :
-- imply
  (vbg_var μ Y * vbg_cov μ X Z - vbg_cov μ X Y * vbg_cov μ Y Z) * (vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X) = (vbg_exp μ Y * vbg_covPlus μ Y X Z + (1 - vbg_exp μ Y) * vbg_covMinus μ Y X Z) * (vbg_var μ X * vbg_var μ Y - vbg_cov μ X Y ^ 2) := by
-- proof
  apply StatMech.Walls.VBG.vbg_prop1 μ X Y Z hY hp0 hp1

/--
[vbg_cov_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cov_centered_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {f g : Ω → ℝ}
-- given
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  vbg_cov μ f g = ∑ ω, μ ω * ((f ω - vbg_exp μ f) * (g ω - vbg_exp μ g)) := by
-- proof
  apply StatMech.Walls.VBG.vbg_cov_centered μ X Y Z μ hμ f g

/--
[vbg_var_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_var_nonneg_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {f : Ω → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  0 ≤ vbg_var μ f := by
-- proof
  apply StatMech.Walls.VBG.vbg_var_nonneg μ X Y Z μ hμ0 hμ f

/--
[vbg_cauchy_schwarz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cauchy_schwarz_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {f g : Ω → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  vbg_cov μ f g ^ 2 ≤ vbg_var μ f * vbg_var μ g := by
-- proof
  apply StatMech.Walls.VBG.vbg_cauchy_schwarz μ X Y Z μ hμ0 hμ f g

/--
[vbg_condPlus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_condPlus_nonneg_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {π Y : Ω → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hY0 : 0 ≤ Y)
  (hp0 : 0 < vbg_exp π Y) :
-- imply
  0 ≤ vbg_condPlus π Y := by
-- proof
  apply StatMech.Walls.VBG.vbg_condPlus_nonneg μ X Y Z hπ0 hY0 hp0

/--
[vbg_condPlus_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_condPlus_norm_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {π Y : Ω → ℝ}
-- given
  (hp0 : 0 < vbg_exp π Y) :
-- imply
  ∑ ω, vbg_condPlus π Y ω = 1 := by
-- proof
  apply StatMech.Walls.VBG.vbg_condPlus_norm μ X Y Z hp0

/--
[vbg_exp_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_exp_one_sub_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {π Y : Ω → ℝ}
-- given
  (hπ : ∑ ω, π ω = 1) :
-- imply
  vbg_exp π (fun ω => 1 - Y ω) = 1 - vbg_exp π Y := by
-- proof
  apply StatMech.Walls.VBG.vbg_exp_one_sub μ X Y Z hπ

/--
[vbg_condMinus_eq_condPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_condMinus_eq_condPlus_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {π Y : Ω → ℝ}
-- given
  (hπ : ∑ ω, π ω = 1) :
-- imply
  vbg_condMinus π Y = vbg_condPlus π (fun ω => 1 - Y ω) := by
-- proof
  apply StatMech.Walls.VBG.vbg_condMinus_eq_condPlus μ X Y Z hπ

/--
[vbg_ae_const_of_var_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_ae_const_of_var_zero_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {f : Ω → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ : ∑ ω, μ ω = 1)
  (hvar : vbg_var μ f = 0) :
-- imply
  ∀ ω, μ ω * (f ω - vbg_exp μ f) = 0 := by
-- proof
  apply StatMech.Walls.VBG.vbg_ae_const_of_var_zero μ X Y Z μ X Y Z hμ0 hμ f hvar

/--
[vbg_thm1_degenerate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_thm1_degenerate_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ : ∑ ω, μ ω = 1)
  (hY : ∀ ω, Y ω * Y ω = Y ω)
  (hp0 : 0 < vbg_exp μ Y)
  (hp1 : vbg_exp μ Y < 1)
  (hVP : vbg_varPlus μ Y X = 0)
  (hVM : vbg_varMinus μ Y X = 0) :
-- imply
  vbg_var μ Y * vbg_cov μ X Z = vbg_cov μ X Y * vbg_cov μ Y Z := by
-- proof
  apply StatMech.Walls.VBG.vbg_thm1_degenerate μ X Y Z μ X Y Z hμ0 hμ hY hp0 hp1 hVP hVM

/--
[vbg_thm1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_thm1_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ : ∑ ω, μ ω = 1)
  (hY : ∀ ω, Y ω * Y ω = Y ω)
  (hp0 : 0 < vbg_exp μ Y)
  (hp1 : vbg_exp μ Y < 1)
  (hCovP : 0 ≤ vbg_covPlus μ Y X Z)
  (hCovM : 0 ≤ vbg_covMinus μ Y X Z)
  (hnondeg : 0 < vbg_exp μ Y * vbg_varPlus μ Y X + (1 - vbg_exp μ Y) * vbg_varMinus μ Y X) :
-- imply
  vbg_cov μ X Y * vbg_cov μ Y Z ≤ vbg_var μ Y * vbg_cov μ X Z := by
-- proof
  apply StatMech.Walls.VBG.vbg_thm1 μ X Y Z μ X Y Z hμ0 hμ hY hp0 hp1 hCovP hCovM hnondeg

/--
[vbg_coordUp_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_coordUp_idem_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {j : E}
  {ω : ConfigSpace E} :
-- imply
  vbg_coordUp j ω * vbg_coordUp j ω = vbg_coordUp j ω := by
-- proof
  apply StatMech.Walls.VBG.vbg_coordUp_idem μ X Y Z j ω

/--
[vbg_coordDown_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_coordDown_idem_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {j : E}
  {ω : ConfigSpace E} :
-- imply
  vbg_coordDown j ω * vbg_coordDown j ω = vbg_coordDown j ω := by
-- proof
  apply StatMech.Walls.VBG.vbg_coordDown_idem μ X Y Z j ω

/--
[vbg_sup_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_sup_apply_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {ω ω' : ConfigSpace E}
  {e : E} :
-- imply
  (ω ⊔ ω') e = (ω e || ω' e) := by
-- proof
  apply StatMech.Walls.VBG.vbg_sup_apply μ X Y Z ω ω' e

/--
[vbg_inf_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_inf_apply_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {ω ω' : ConfigSpace E}
  {e : E} :
-- imply
  (ω ⊓ ω') e = (ω e && ω' e) := by
-- proof
  apply StatMech.Walls.VBG.vbg_inf_apply μ X Y Z ω ω' e

/--
[vbg_coordUp_logSupermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_coordUp_logSupermod_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {j : E}
  {ω ω' : ConfigSpace E} :
-- imply
  vbg_coordUp j ω * vbg_coordUp j ω' ≤ vbg_coordUp j (ω ⊔ ω') * vbg_coordUp j (ω ⊓ ω') := by
-- proof
  apply StatMech.Walls.VBG.vbg_coordUp_logSupermod μ X Y Z j ω ω'

/--
[vbg_coordDown_logSupermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_coordDown_logSupermod_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {j : E}
  {ω ω' : ConfigSpace E} :
-- imply
  vbg_coordDown j ω * vbg_coordDown j ω' ≤ vbg_coordDown j (ω ⊔ ω') * vbg_coordDown j (ω ⊓ ω') := by
-- proof
  apply StatMech.Walls.VBG.vbg_coordDown_logSupermod μ X Y Z j ω ω'

/--
[vbg_mul_logSupermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_mul_logSupermod_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {π Y : ConfigSpace E → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hY0 : 0 ≤ Y)
  (hπ : FKGLatticeCondition π)
  (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω')) :
-- imply
  FKGLatticeCondition (fun ω => π ω * Y ω) := by
-- proof
  apply StatMech.Walls.VBG.vbg_mul_logSupermod μ X Y Z hπ0 hY0 hπ hY

/--
[vbg_div_const_logSupermod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_div_const_logSupermod_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {ρ : ConfigSpace E → ℝ}
  {c : ℝ}
-- given
  (hc : 0 < c)
  (hρ : FKGLatticeCondition ρ) :
-- imply
  FKGLatticeCondition (fun ω => ρ ω / c) := by
-- proof
  apply StatMech.Walls.VBG.vbg_div_const_logSupermod μ X Y Z c hc hρ

/--
[vbg_condPlus_FKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_condPlus_FKG_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {π Y : ConfigSpace E → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hY0 : 0 ≤ Y)
  (hπ : FKGLatticeCondition π)
  (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
  (hp0 : 0 < vbg_exp π Y) :
-- imply
  FKGLatticeCondition (vbg_condPlus π Y) := by
-- proof
  apply StatMech.Walls.VBG.vbg_condPlus_FKG μ X Y Z hπ0 hY0 hπ hY hp0

/--
[vbg_covPlus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_covPlus_nonneg_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {π Y f g : ConfigSpace E → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hY0 : 0 ≤ Y)
  (hπ : FKGLatticeCondition π)
  (hY : ∀ ω ω', Y ω * Y ω' ≤ Y (ω ⊔ ω') * Y (ω ⊓ ω'))
  (hp0 : 0 < vbg_exp π Y)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  0 ≤ vbg_covPlus π Y f g := by
-- proof
  apply StatMech.Walls.VBG.vbg_covPlus_nonneg μ X Y Z hπ0 hY0 hπ hY hp0 hf hg

/--
[vbg_covMinus_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_covMinus_nonneg_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {π Y f g : ConfigSpace E → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hπnorm : ∑ ω, π ω = 1)
  (hYbnd : ∀ ω, Y ω ≤ 1)
  (hπ : FKGLatticeCondition π)
  (hYc : ∀ ω ω', (1 - Y ω) * (1 - Y ω') ≤ (1 - Y (ω ⊔ ω')) * (1 - Y (ω ⊓ ω')))
  (hp1 : vbg_exp π Y < 1)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  0 ≤ vbg_covMinus π Y f g := by
-- proof
  apply StatMech.Walls.VBG.vbg_covMinus_nonneg μ X Y Z hπ0 hπnorm hYbnd hπ hYc hp1 hf hg

/--
[vbg_thm1_configSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_thm1_configSpace_eq
  [Fintype Ω]
  {μ : Ω → ℝ}
  {X Y Z : Ω → ℝ}
  [Fintype E]
  [DecidableEq E]
  {π : ConfigSpace E → ℝ}
  {j : E}
  {X Z : ConfigSpace E → ℝ}
-- given
  (hπ0 : 0 ≤ π)
  (hπnorm : ∑ ω, π ω = 1)
  (hπ : FKGLatticeCondition π)
  (hX : Monotone X)
  (hZ : Monotone Z)
  (hp0 : 0 < vbg_exp π (vbg_coordUp j))
  (hp1 : vbg_exp π (vbg_coordUp j) < 1) :
-- imply
  vbg_cov π X (vbg_coordUp j) * vbg_cov π (vbg_coordUp j) Z ≤ vbg_var π (vbg_coordUp j) * vbg_cov π X Z := by
-- proof
  apply StatMech.Walls.VBG.vbg_thm1_configSpace μ X Y Z hπ0 hπnorm hπ j hX hZ hp0 hp1

/--
[vbg_isingExp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_isingExp_eq_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h f = vbg_exp (isingProb G β h) f := by
-- proof
  apply StatMech.Walls.VBG.vbg_isingExp_eq G β h f

/--
[vbg_cov2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cov2_eq_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ) :
-- imply
  cov2 G β h x y = vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s y) := by
-- proof
  apply StatMech.Walls.VBG.vbg_cov2_eq G β h x y

/--
[vbg_spin_eq_coordUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_spin_eq_coordUp_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j : V}
  {s : ConfigSpace V} :
-- imply
  spin s j = 2 * vbg_coordUp j s - 1 := by
-- proof
  apply StatMech.Walls.VBG.vbg_spin_eq_coordUp G j s

/--
[vbg_spin_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_spin_monotone_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j : V} :
-- imply
  Monotone (fun s : ConfigSpace V => spin s j) := by
-- proof
  apply StatMech.Walls.VBG.vbg_spin_monotone G j

/--
[vbg_cov_affine_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cov_affine_right_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ConfigSpace V → ℝ}
  {f g : ConfigSpace V → ℝ}
  {a b : ℝ}
-- given
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  vbg_cov μ f (fun ω => a * g ω + b) = a * vbg_cov μ f g := by
-- proof
  apply StatMech.Walls.VBG.vbg_cov_affine_right G μ hμ f g a b

/--
[vbg_cov_affine_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cov_affine_left_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {μ : ConfigSpace V → ℝ}
  {f g : ConfigSpace V → ℝ}
  {a b : ℝ}
-- given
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  vbg_cov μ (fun ω => a * f ω + b) g = a * vbg_cov μ f g := by
-- proof
  apply StatMech.Walls.VBG.vbg_cov_affine_left G μ hμ f g a b

/--
[vbg_cov_spin_coordUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cov_spin_coordUp_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x j : V}
-- given
  (β h : ℝ) :
-- imply
  vbg_cov (isingProb G β h) (fun s => spin s x) (fun s => spin s j) = 2 * vbg_cov (isingProb G β h) (fun s => spin s x) (vbg_coordUp j) := by
-- proof
  apply StatMech.Walls.VBG.vbg_cov_spin_coordUp G β h x j

/--
[vbg_ising_coordUp_pos_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_ising_coordUp_pos_lt_one_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {j : V}
-- given
  (β h : ℝ) :
-- imply
  0 < vbg_exp (isingProb G β h) (vbg_coordUp j) ∧ vbg_exp (isingProb G β h) (vbg_coordUp j) < 1 := by
-- proof
  apply StatMech.Walls.VBG.vbg_ising_coordUp_pos_lt_one G β h j

/--
[vbg_cor1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cor1_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  cov2 G β h i j * cov2 G β h j k ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k := by
-- proof
  apply StatMech.Walls.VBG.vbg_cor1 G β h hβ i j k

/--
[mc_Y_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma mc_Y_idem_eq
  [Fintype Ω] :
-- imply
  ∀ ω, mcY ω * mcY ω = mcY ω := by
-- proof
  apply StatMech.Walls.VBG.mc_Y_idem

/--
[mc_p_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma mc_p_pos_eq
  [Fintype Ω] :
-- imply
  0 < vbg_exp mcMu mcY := by
-- proof
  apply StatMech.Walls.VBG.mc_p_pos

/--
[mc_p_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma mc_p_lt_one_eq
  [Fintype Ω] :
-- imply
  vbg_exp mcMu mcY < 1 := by
-- proof
  apply StatMech.Walls.VBG.mc_p_lt_one

/--
[mc_prop1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma mc_prop1_eq
  [Fintype Ω] :
-- imply
  (vbg_var mcMu mcY * vbg_cov mcMu mcX mcZ - vbg_cov mcMu mcX mcY * vbg_cov mcMu mcY mcZ) * (vbg_exp mcMu mcY * vbg_varPlus mcMu mcY mcX + (1 - vbg_exp mcMu mcY) * vbg_varMinus mcMu mcY mcX) = (vbg_exp mcMu mcY * vbg_covPlus mcMu mcY mcX mcZ + (1 - vbg_exp mcMu mcY) * vbg_covMinus mcMu mcY mcX mcZ) * (vbg_var mcMu mcX * vbg_var mcMu mcY - vbg_cov mcMu mcX mcY ^ 2) := by
-- proof
  apply StatMech.Walls.VBG.mc_prop1

/--
[vbg_ghs_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_ghs_distinct_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v : V}
-- given
  (β h : ℝ) :
-- imply
  StatMech.Walls.GhcEqGap.eg_ursell3 G β h v v v = 2 * (isingExpectation G β h (fun s => spin s v))^3 - 2 * isingExpectation G β h (fun s => spin s v) := by
-- proof
  apply StatMech.Walls.VBG.vbg_ghs_distinct G β h v

/--
[vbg_cor1_arbitrary_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_cor1_arbitrary_field_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β) :
-- imply
  cov2 G β h i j * cov2 G β h j k ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k := by
-- proof
  apply StatMech.Walls.VBG.vbg_cor1_arbitrary_field G β h hβ i j k

/--
[vbg_ghs_relationship_notes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean)
-/
@[path]
private lemma vbg_ghs_relationship_notes_eq
  [Fintype Ω]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  True := by
-- proof
  apply StatMech.Walls.VBG.vbg_ghs_relationship_notes G


-- created on 2026-10-23

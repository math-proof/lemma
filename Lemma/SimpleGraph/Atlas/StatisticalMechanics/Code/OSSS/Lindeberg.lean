import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
open Finset StatMech StatMech.OSSS StatMech.OSSS.Lindeberg


/--
[mean_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_add_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (g h : ConfigSpace E → ℝ) :
-- imply
  mean μ (fun ω => g ω + h ω) = mean μ g + mean μ h := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_add μ g h

/--
[mean_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_sub_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (g h : ConfigSpace E → ℝ) :
-- imply
  mean μ (fun ω => g ω - h ω) = mean μ g - mean μ h := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_sub μ g h

/--
[mean_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_const_mul_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {c : ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  mean μ (fun ω => c * g ω) = c * mean μ g := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_const_mul μ c g

/--
[mean_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_const_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {c : ℝ}
-- given
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  mean μ (fun _ => c) = c := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_const μ hμ c

/--
[var_eq_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma var_eq_double_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hμ : ∑ ω, μ ω = 1) :
-- imply
  var μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
-- proof
  apply StatMech.OSSS.Lindeberg.var_eq_double_sum μ hμ f

/--
[cExp_Fmeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_Fmeas_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ} :
-- imply
  Fmeas F (cExp μ F g) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_Fmeas μ F g

/--
[cExp_pullout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_pullout_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (g h : ConfigSpace E → ℝ)
  (hh : Fmeas F h) :
-- imply
  (∑ ω, (cExp μ F g ω * h ω) * μ ω) = ∑ ω, (g ω * h ω) * μ ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_pullout hpos F g h hh

/--
[mean_cExp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_cExp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  mean μ (cExp μ F g) = mean μ g := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_cExp hpos F g

/--
[cExp_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_mono_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (hg : Monotone g)
  (hg0 : 0 ≤ g) :
-- imply
  Monotone (cExp μ F g) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_mono hpos hFKG F hg hg0

/--
[mean_mul_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma mean_mul_ge_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A B : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hA : Monotone A)
  (hB : Monotone B) :
-- imply
  mean μ A * mean μ B ≤ mean μ (fun ω => A ω * B ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.mean_mul_ge hpos hμ1 hFKG hA hB

/--
[cExp_eq_cSum_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_eq_cSum_div_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  cExp μ F g ω = cSum μ F g ω / condNorm μ F ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_eq_cSum_div μ F g ω

/--
[condNorm_eq_cSum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma condNorm_eq_cSum_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {ω : ConfigSpace E} :
-- imply
  condNorm μ F ω = cSum μ F (fun _ => 1) ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.condNorm_eq_cSum_one μ F ω

/--
[cSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cSum_split_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (he : e ∉ F) :
-- imply
  cSum μ F g ω = cSum μ (insert e F) g (setOpen e ω) + cSum μ (insert e F) g (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cSum_split μ F e he g ω

/--
[cSum_coord_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cSum_coord_open_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setOpen e ω) = cSum μ (insert e F) g (setOpen e ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cSum_coord_open μ F e g ω

/--
[cSum_coord_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cSum_coord_closed_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  cSum μ (insert e F) (fun ω'' => g ω'' * coord e ω'') (setClosed e ω) = 0 := by
-- proof
  apply StatMech.OSSS.Lindeberg.cSum_coord_closed μ F e g ω

/--
[cExp_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_decomp_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (he : e ∉ F) :
-- imply
  cExp μ F f ω = cExp μ F (coord e) ω * cExp μ (insert e F) f (setOpen e ω) + (1 - cExp μ F (coord e) ω) * cExp μ (insert e F) f (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_decomp hpos F e he f ω

/--
[coord_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma coord_mono_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  Monotone (coord (E := E) e) := by
-- proof
  apply StatMech.OSSS.Lindeberg.coord_mono e

/--
[coord_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma coord_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  (0 : ConfigSpace E → ℝ) ≤ coord e := by
-- proof
  apply StatMech.OSSS.Lindeberg.coord_nonneg e

/--
[cExp_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hg0 : 0 ≤ g) :
-- imply
  0 ≤ cExp μ F g ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_nonneg hpos F hg0 ω

/--
[cExp_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {g : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hg1 : ∀ ω, g ω ≤ 1) :
-- imply
  cExp μ F g ω ≤ 1 := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_le_one hpos F hg1 ω

/--
[delta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma delta_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f) :
-- imply
  0 ≤ delta μ F e f ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.delta_nonneg hpos hFKG F e hf hf0 ω

/--
[delta_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma delta_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hf1 : ∀ ω, f ω ≤ 1)
  (hf0 : 0 ≤ f) :
-- imply
  delta μ F e f ω ≤ 1 := by
-- proof
  apply StatMech.OSSS.Lindeberg.delta_le_one hpos F e hf1 hf0 ω

/--
[delta_Fmeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma delta_Fmeas_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
-- given
  (he : e ∉ F) :
-- imply
  Fmeas F (delta μ F e f) := by
-- proof
  apply StatMech.OSSS.Lindeberg.delta_Fmeas μ F e he f

/--
[cExp_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_branch_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E} :
-- imply
  cExp μ (insert e F) f ω = if ω e then cExp μ (insert e F) f (setOpen e ω) else cExp μ (insert e F) f (setClosed e ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_branch μ F e f ω

/--
[step_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma step_factor_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (he : e ∉ F) :
-- imply
  cExp μ (insert e F) f ω - cExp μ F f ω = delta μ F e f ω * (coord e ω - cExp μ F (coord e) ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.step_factor hpos F e he f ω

/--
[step_le_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma step_le_cov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {e : E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (he : e ∉ F)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  mean μ (fun ω => (cExp μ (insert e F) f ω - cExp μ F f ω) ^ 2) ≤ cov μ f (coord e) := by
-- proof
  apply StatMech.OSSS.Lindeberg.step_le_cov hpos hμ1 hFKG F e he hf hf0 hf1

/--
[Fmeas_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma Fmeas_mono_eq
  [Fintype E]
  [DecidableEq E]
  {F F' : Finset E}
  {h : ConfigSpace E → ℝ}
-- given
  (hsub : F ⊆ F')
  (hh : Fmeas F h) :
-- imply
  Fmeas F' h := by
-- proof
  apply StatMech.OSSS.Lindeberg.Fmeas_mono hsub hh

/--
[cExp_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_univ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  cExp μ Finset.univ f ω = f ω := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_univ hpos f ω

/--
[cExp_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cExp_empty_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
  {ω : ConfigSpace E}
-- given
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  cExp μ ∅ f ω = mean μ f := by
-- proof
  apply StatMech.OSSS.Lindeberg.cExp_empty hμ1 f ω

/--
[projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma projection_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F F' : Finset E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hsub : F ⊆ F') :
-- imply
  mean μ (fun ω => cExp μ F' f ω * cExp μ F f ω) = mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.projection hpos hsub f

/--
[pythagoras](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma pythagoras_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F F' : Finset E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hsub : F ⊆ F') :
-- imply
  mean μ (fun ω => (cExp μ F' f ω - cExp μ F f ω) ^ 2) = mean μ (fun ω => cExp μ F' f ω * cExp μ F' f ω) - mean μ (fun ω => cExp μ F f ω * cExp μ F f ω) := by
-- proof
  apply StatMech.OSSS.Lindeberg.pythagoras hpos hsub f

/--
[var_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma var_telescope_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : Fin n ≃ E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  var μ f = ∑ t ∈ Finset.range n, mean μ (fun ω => (cExp μ (prefixSet (σ : Fin n → E) (t + 1)) f ω - cExp μ (prefixSet (σ : Fin n → E) t) f ω) ^ 2) := by
-- proof
  apply StatMech.OSSS.Lindeberg.var_telescope hpos hμ1 σ f

/--
[monotonic_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma monotonic_poincare_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  var μ f ≤ ∑ e, cov μ f (coord e) := by
-- proof
  apply StatMech.OSSS.Lindeberg.monotonic_poincare hpos hμ1 hFKG hf hf0 hf1

/--
[cov_eq_genCov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma cov_eq_genCov_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f g : ConfigSpace E → ℝ} :
-- imply
  cov μ f g = genCov μ f g := by
-- proof
  apply StatMech.OSSS.Lindeberg.cov_eq_genCov μ f g

/--
[var_eq_genVar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma var_eq_genVar_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ} :
-- imply
  var μ g = genVar μ g := by
-- proof
  apply StatMech.OSSS.Lindeberg.var_eq_genVar μ g

/--
[coord_eq_genCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma coord_eq_genCoord_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  (coord e : ConfigSpace E → ℝ) = genCoord e := by
-- proof
  apply StatMech.OSSS.Lindeberg.coord_eq_genCoord e

/--
[monotonicOSSSBound_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma monotonicOSSSBound_poincare_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  MonotonicOSSSBound μ Finset.univ f 1 1 1 := by
-- proof
  apply StatMech.OSSS.Lindeberg.monotonicOSSSBound_poincare hpos hμ1 hFKG hf hf0 hf1

/--
[fk_monotonic_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma fk_monotonic_poincare_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  var (fkMass G p q) f ≤ ∑ e, cov (fkMass G p q) f (coord e) := by
-- proof
  apply StatMech.OSSS.Lindeberg.fk_monotonic_poincare G hp hp1 hq hf hf0 hf1

/--
[fk_monotonicOSSSBound_poincare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean)
-/
@[path]
private lemma fk_monotonicOSSSBound_poincare_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  MonotonicOSSSBound (fkMass G p q) Finset.univ f 1 1 1 := by
-- proof
  apply StatMech.OSSS.Lindeberg.fk_monotonicOSSSBound_poincare G hp hp1 hq hf hf0 hf1


-- created on 2026-10-23

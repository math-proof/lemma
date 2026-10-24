import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.FiniteProperParabolicsInstance
open Finset BigOperators CoxeterGroup TitsCone


/--
[standard](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma standard_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {α : B → ℝ}
-- given
  (hα : α ∈ standardΦpos M) :
-- imply
  CoxeterGroup.bilinForm M α α = 1 := by
-- proof
  apply standardΦpos_form_eq_one M α hα

/--
[finiteRoots_in_subspan_of_AffineCoxeterHyp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma finiteRoots_in_subspan_of_AffineCoxeterHyp_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
-- given
  (hyp : AffineCoxeterHyp M) :
-- imply
  ∀ (I : Finset B), I ≠ Finset.univ → Set.Finite {α ∈ standardΦpos M | ∀ s : B, s ∉ I → α s = 0} := by
-- proof
  apply TitsCone.finiteRoots_in_subspan_of_AffineCoxeterHyp M hyp

/--
[bilinForm_radical_shift_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma bilinForm_radical_shift_eq_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ w : B → ℝ}
  {a : ℝ}
-- given
  (hrad : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  ∑ s, ∑ t, (w s - a * v₀ s) * CoxeterGroup.formVal M s t * (w t - a * v₀ t) = ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := by
-- proof
  apply TitsCone.bilinForm_radical_shift_eq M v₀ w a hrad

/--
[norm_sq_le_of_perp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma norm_sq_le_of_perp_shift_eq
  [DecidableEq B]
  [Fintype B]
  {v₀ w : B → ℝ}
  {a : ℝ}
-- given
  (hperp : ∑ s, v₀ s * w s = 0) :
-- imply
  ∑ s, w s ^ 2 ≤ ∑ s, (w s - a * v₀ s) ^ 2 := by
-- proof
  apply TitsCone.norm_sq_le_of_perp_shift v₀ w a hperp

/--
[bilinForm_on_v0_perp_coercive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma bilinForm_on_v0_perp_coercive_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ : B → ℝ}
-- given
  (hyp : AffineCoxeterHyp M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0) :
-- imply
  ∃ c_min : ℝ, c_min > 0 ∧ ∀ w : B → ℝ, (∑ s, v₀ s * w s = 0) → c_min * ∑ s, w s ^ 2 ≤ ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t := by
-- proof
  apply TitsCone.bilinForm_on_v0_perp_coercive M hyp v₀ hv₀_pos hv₀_radical

/--
[abs_inner_le_sqrt_norms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma abs_inner_le_sqrt_norms_eq
  [DecidableEq B]
  [Fintype B]
  {a b : B → ℝ}
  {C : ℝ}
-- given
  (hC : 0 ≤ C)
  (ha : ∑ s, (a s) ^ 2 ≤ C) :
-- imply
  |∑ s, a s * b s| ≤ Real.sqrt C * Real.sqrt (∑ s, (b s) ^ 2) := by
-- proof
  apply TitsCone.abs_inner_le_sqrt_norms a b hC ha

/--
[sum_sq_orth_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma sum_sq_orth_decomp_eq
  [DecidableEq B]
  [Fintype B]
  {v₀ w : B → ℝ}
  {c : ℝ}
-- given
  (hperp : ∑ s, v₀ s * w s = 0) :
-- imply
  ∑ s : B, (c * v₀ s + w s) ^ 2 = c ^ 2 * ∑ s, (v₀ s) ^ 2 + ∑ s, (w s) ^ 2 := by
-- proof
  apply TitsCone.sum_sq_orth_decomp v₀ w c hperp

/--
[nonposRoots_coord_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma nonposRoots_coord_bound_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ x : B → ℝ}
-- given
  (hyp : AffineCoxeterHyp M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx_hyp : ∑ s, v₀ s * x s = 1)
  (hcoercive : ∃ c_min : ℝ, c_min > 0 ∧ ∀ w : B → ℝ, (∑ s, v₀ s * w s = 0) → c_min * ∑ s, w s ^ 2 ≤ ∑ s, ∑ t, w s * CoxeterGroup.formVal M s t * w t) :
-- imply
  ∃ C : ℝ, ∀ α ∈ nonposRoots (standardΦpos M) x, ∀ s : B, α s ≤ C ∧ 0 ≤ α s := by
-- proof
  apply TitsCone.nonposRoots_coord_bound M hyp v₀ hv₀_pos hv₀_radical x hx_hyp hcoercive

/--
[hyperplane_nonposRoots_finite_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/FiniteProperParabolicsInstance.lean)
-/
@[path]
private lemma hyperplane_nonposRoots_finite_axiom_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v₀ x : B → ℝ}
-- given
  (hyp : AffineCoxeterHyp M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_radical : ∀ t : B, ∑ u : B, v₀ u * CoxeterGroup.formVal M u t = 0)
  (hx_hyp : ∑ s, v₀ s * x s = 1) :
-- imply
  Set.Finite (nonposRoots (standardΦpos M) x) := by
-- proof
  apply TitsCone.hyperplane_nonposRoots_finite_axiom M hyp v₀ hv₀_pos hv₀_radical x hx_hyp


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.NormalFamilies

open Complex.NormalFamilies Set Filter Topology

/--
[isLocallyUniformlyBoundedOn_of_forall_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalFamilies.lean)
-/
@[path]
private lemma is_locally_uniformly_bounded_on_of_forall_norm_le_eq
-- given
  {U : Set ℂ} {F : ℕ → ℂ → ℂ} {C : ℝ}
  (hU : IsOpen U)
  (hC : 0 ≤ C)
  (hF : ∀ n, ∀ y ∈ U, ‖F n y‖ ≤ C) :
-- imply
  IsLocallyUniformlyBoundedOn U F := by
-- proof
  apply isLocallyUniformlyBoundedOn_of_forall_norm_le hU hC hF

/--
[IsLocallyUniformlyBoundedOn.exists_bound_of_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalFamilies.lean)
-/
@[path]
private lemma is_locally_uniformly_bounded_on_exists_bound_of_is_compact_eq
-- given
  {U K : Set ℂ} {F : ℕ → ℂ → ℂ}
  (hB : IsLocallyUniformlyBoundedOn U F)
  (hKU : K ⊆ U)
  (hKc : IsCompact K) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ y ∈ K, ‖F n y‖ ≤ C := by
-- proof
  apply IsLocallyUniformlyBoundedOn.exists_bound_of_isCompact hB hKU hKc

/--
[montel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalFamilies.lean)
-/
@[path]
private lemma montel_eq
-- given
  {U : Set ℂ}
  (F : ℕ → ℂ → ℂ)
  (hU : IsOpen U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (hB : IsLocallyUniformlyBoundedOn U F) :
-- imply
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
    TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop U := by
-- proof
  apply montel hU F hF hB

/--
[vitali](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/NormalFamilies.lean)
-/
@[path]
private lemma vitali_eq
-- given
  {U S : Set ℂ}
  (F : ℕ → ℂ → ℂ)
  (g : ℂ → ℂ)
  (hU : IsOpen U)
  (hUc : IsPreconnected U)
  (hF : ∀ n, DifferentiableOn ℂ (F n) U)
  (hB : IsLocallyUniformlyBoundedOn U F)
  (hS : S ⊆ U)
  (hAcc : ∃ x0 ∈ U, AccPt x0 (Filter.principal S))
  (hg : ∀ z ∈ S, Tendsto (fun n => F n z) atTop (nhds (g z))) :
-- imply
  ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ (∀ z ∈ S, f z = g z) ∧
    TendstoLocallyUniformlyOn F f atTop U := by
-- proof
  apply vitali hU hUc F hF hB hS hAcc g hg


-- created on 2026-10-09

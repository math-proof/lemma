import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.SLE.ChainCapacity.Part2
open Complex Set Filter Topology MeasureTheory StatMech StatMech.SLE


/--
[IsCapacityParametrized.coeff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma coeff_zero_eq
  {c : LoewnerChain}
  {a₁ : ℝ → ℝ}
-- given
  (h : IsCapacityParametrized c a₁) :
-- imply
  a₁ 0 = 0 := by
-- proof
  apply StatMech.SLE.IsCapacityParametrized.coeff_zero h

/--
[chordalSLE_capacity_parametrized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_capacity_parametrized_eq
  {c : CapacityParametrizedChain} :
-- imply
  ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (c.chain.maps t) (2 * t) := by
-- proof
  apply StatMech.SLE.chordalSLE_capacity_parametrized c

/--
[loewnerChain_hulls_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma loewnerChain_hulls_increasing_eq
  {c : CapacityParametrizedChain} :
-- imply
  MonotoneHullFamily c.hull := by
-- proof
  apply StatMech.SLE.loewnerChain_hulls_increasing c

/--
[chordalSLE_hull_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_hull_subset_eq
  {c : CapacityParametrizedChain}
  {s t : ℝ}
-- given
  (hst : s ≤ t) :
-- imply
  c.hull s ⊆ c.hull t := by
-- proof
  apply StatMech.SLE.chordalSLE_hull_subset c hst

/--
[chordalSLE_complement_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_complement_antitone_eq
  {c : CapacityParametrizedChain} :
-- imply
  Antitone (fun t => upperHalfPlane \ c.hull t) := by
-- proof
  apply StatMech.SLE.chordalSLE_complement_antitone c

/--
[chordalSLE_hcap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_hcap_eq_eq
  {c : CapacityParametrizedChain} :
-- imply
  ∀ t ∈ Ici (0 : ℝ), c.coeff t = 2 * t := by
-- proof
  apply StatMech.SLE.chordalSLE_hcap_eq c

/--
[chordalSLE_normalized_map_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_normalized_map_unique_eq
  {c : CapacityParametrizedChain}
  {t : ℝ}
  {b : ℝ}
-- given
  (ht : t ∈ Ici (0 : ℝ))
  (hb : HasHalfPlaneCapacity (c.chain.maps t) b) :
-- imply
  b = 2 * t := by
-- proof
  apply StatMech.SLE.chordalSLE_normalized_map_unique c ht hb

/--
[chordalSLE_hcap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_hcap_zero_eq
  {c : CapacityParametrizedChain} :
-- imply
  HasHalfPlaneCapacity (c.chain.maps 0) 0 := by
-- proof
  apply StatMech.SLE.chordalSLE_hcap_zero c

/--
[continuous_sleDriving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma continuous_sleDriving_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
-- given
  (hcont : Continuous fun t => B t ω) :
-- imply
  Continuous (sleDriving κ B ω) := by
-- proof
  apply StatMech.SLE.continuous_sleDriving κ B ω hcont

/--
[loewnerChain_of_sle_realization_maps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma loewnerChain_of_sle_realization_maps_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
  {g : ℝ → ℂ → ℂ}
-- given
  (hcont : Continuous fun t => B t ω)
  (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
-- imply
  (loewnerChain_of_sle_realization κ B ω g hcont hloe).maps = g := by
-- proof
  apply StatMech.SLE.loewnerChain_of_sle_realization_maps κ B ω g hcont hloe

/--
[loewnerChain_of_sle_realization_driving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma loewnerChain_of_sle_realization_driving_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
  {g : ℝ → ℂ → ℂ}
-- given
  (hcont : Continuous fun t => B t ω)
  (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
-- imply
  (loewnerChain_of_sle_realization κ B ω g hcont hloe).driving = sleDriving κ B ω := by
-- proof
  apply StatMech.SLE.loewnerChain_of_sle_realization_driving κ B ω g hcont hloe

/--
[chordalSLE_realization_capacity_parametrized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean)
-/
@[path]
private lemma chordalSLE_realization_capacity_parametrized_eq
  {κ : ℝ}
  {B : ℝ → Ω → ℝ}
  {ω : Ω}
  {g : ℝ → ℂ → ℂ}
  {a₁ : ℝ → ℝ}
-- given
  (hcont : Continuous fun t => B t ω)
  (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g)
  (hnorm : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
  (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
-- imply
  ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) := by
-- proof
  apply StatMech.SLE.chordalSLE_realization_capacity_parametrized κ B ω g hcont hloe hnorm hrate


-- created on 2026-10-23

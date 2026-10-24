import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneReal
open Finset StatMech StatMech.FrontierA


/--
[realUpperLevel_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma realUpperLevel_isIncreasing_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E -> ℝ}
  {a : ℝ}
-- given
  (hf : Monotone f) :
-- imply
  IsIncreasing (realUpperLevel f a) := by
-- proof
  apply StatMech.FrontierA.realUpperLevel_isIncreasing hf a

/--
[realLayer_increment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma realLayer_increment_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E -> ℝ}
  {layer : ℝ × ℝ}
-- given
  (hf : ∀ omega, 0 ≤ f omega)
  (hlayer : layer ∈ realLayerSet f) :
-- imply
  0 ≤ layer.2 := by
-- proof
  apply StatMech.FrontierA.realLayer_increment_nonneg hf hlayer

/--
[real_value_eq_layer_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma real_value_eq_layer_sum_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E -> ℝ}
  {omega : ConfigSpace E}
-- given
  (hf : ∀ omega, 0 ≤ f omega) :
-- imply
  f omega = ∑ layer ∈ realLayerSet f, layer.2 * eventIndicator (realUpperLevel f layer.1) omega := by
-- proof
  apply StatMech.FrontierA.real_value_eq_layer_sum hf omega

/--
[cylinderMin_mem_realLevels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma cylinderMin_mem_realLevels_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (f : ConfigSpace E -> ℝ) :
-- imply
  cylinderMin f K omega ∈ realLevels f := by
-- proof
  apply StatMech.FrontierA.cylinderMin_mem_realLevels f K omega

/--
[occursOn_realUpperLevel_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma occursOn_realUpperLevel_iff_eq
  [Fintype E]
  [DecidableEq E]
  {a : ℝ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (f : ConfigSpace E -> ℝ) :
-- imply
  OccursOn (realUpperLevel f a) K omega ↔ a ≤ cylinderMin f K omega := by
-- proof
  apply StatMech.FrontierA.occursOn_realUpperLevel_iff f a K omega

/--
[cylinderMin_eq_layer_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma cylinderMin_eq_layer_sum_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E -> ℝ}
  {K : Set E}
  {omega : ConfigSpace E}
-- given
  (hf : ∀ omega, 0 ≤ f omega) :
-- imply
  cylinderMin f K omega = ∑ layer ∈ realLayerSet f, if layer.1 ≤ cylinderMin f K omega then layer.2 else 0 := by
-- proof
  apply StatMech.FrontierA.cylinderMin_eq_layer_sum hf K omega

/--
[cylinderMin_mul_le_realLevelBoxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma cylinderMin_mul_le_realLevelBoxes_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E -> ℝ}
  {K L : Set E}
  {omega : ConfigSpace E}
-- given
  (hf : ∀ omega, 0 ≤ f omega)
  (hg : ∀ omega, 0 ≤ g omega)
  (hKL : Disjoint K L) :
-- imply
  cylinderMin f K omega * cylinderMin g L omega ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g, layerF.2 * layerG.2 * eventIndicator (disjointOccurrence (realUpperLevel f layerF.1) (realUpperLevel g layerG.1)) omega := by
-- proof
  apply StatMech.FrontierA.cylinderMin_mul_le_realLevelBoxes hf hg K L hKL omega

/--
[functionalDisjointMax_real_le_levelBoxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma functionalDisjointMax_real_le_levelBoxes_eq
  [Fintype E]
  [DecidableEq E]
  {f g : ConfigSpace E -> ℝ}
  {omega : ConfigSpace E}
-- given
  (hf : ∀ omega, 0 ≤ f omega)
  (hg : ∀ omega, 0 ≤ g omega) :
-- imply
  functionalDisjointMax f g omega ≤ ∑ layerF ∈ realLayerSet f, ∑ layerG ∈ realLayerSet g, layerF.2 * layerG.2 * eventIndicator (disjointOccurrence (realUpperLevel f layerF.1) (realUpperLevel g layerG.1)) omega := by
-- proof
  apply StatMech.FrontierA.functionalDisjointMax_real_le_levelBoxes hf hg omega

/--
[productExpectation_real_eq_levels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma productExpectation_real_eq_levels_eq
  [Fintype E]
  [DecidableEq E]
  {f : ConfigSpace E -> ℝ}
-- given
  (phi : E -> Bool -> ℝ)
  (hf : ∀ omega, 0 ≤ f omega) :
-- imply
  productExpectation phi f = ∑ layer ∈ realLayerSet f, layer.2 * wprob phi (realUpperLevel f layer.1) := by
-- proof
  apply StatMech.FrontierA.productExpectation_real_eq_levels phi hf

/--
[functionalBKR_monotone_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean)
-/
@[path]
private lemma functionalBKR_monotone_real_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (phi : E -> Bool -> ℝ)
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (f g : ConfigSpace E -> ℝ)
  (hf0 : ∀ omega, 0 ≤ f omega)
  (hg0 : ∀ omega, 0 ≤ g omega)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  productExpectation phi (functionalDisjointMax f g) ≤ productExpectation phi f * productExpectation phi g := by
-- proof
  apply StatMech.FrontierA.functionalBKR_monotone_real phi hphi0 hphi1 f g hf0 hg0 hf hg


-- created on 2026-10-23

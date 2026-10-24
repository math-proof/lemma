import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.Ergodicity
open MeasureTheory StatMech StatMech.ConfigSpace


/--
[shift_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma shift_apply_eq
  [Group G]
  [MulAction G E]
  {g : G}
  {ω : ConfigSpace E}
  {e : E} :
-- imply
  shift g ω e = ω (g⁻¹ • e) := by
-- proof
  apply StatMech.ConfigSpace.shift_apply g ω e

/--
[shift_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma shift_one_eq
  [Group G]
  [MulAction G E] :
-- imply
  (shift (1 : G) : ConfigSpace E → ConfigSpace E) = id := by
-- proof
  apply StatMech.ConfigSpace.shift_one

/--
[shift_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma shift_mul_eq
  [Group G]
  [MulAction G E]
-- given
  (g h : G) :
-- imply
  (shift (g * h) : ConfigSpace E → ConfigSpace E) = shift g ∘ shift h := by
-- proof
  apply StatMech.ConfigSpace.shift_mul g h

/--
[measurable_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma measurable_shift_eq
  [Group G]
  [MulAction G E]
  {g : G} :
-- imply
  Measurable (shift g : ConfigSpace E → ConfigSpace E) := by
-- proof
  apply StatMech.ConfigSpace.measurable_shift g

/--
[continuous_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma continuous_shift_eq
  [Group G]
  [MulAction G E]
  {g : G} :
-- imply
  Continuous (shift g : ConfigSpace E → ConfigSpace E) := by
-- proof
  apply StatMech.ConfigSpace.continuous_shift g

/--
[shift_inv_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma shift_inv_comp_eq
  [Group G]
  [MulAction G E]
  {g : G} :
-- imply
  (shift g⁻¹ : ConfigSpace E → ConfigSpace E) ∘ shift g = id := by
-- proof
  apply StatMech.ConfigSpace.shift_inv_comp g

/--
[shift_comp_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma shift_comp_inv_eq
  [Group G]
  [MulAction G E]
  {g : G} :
-- imply
  (shift g : ConfigSpace E → ConfigSpace E) ∘ shift g⁻¹ = id := by
-- proof
  apply StatMech.ConfigSpace.shift_comp_inv g

/--
[IsErgodic.isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma isTranslationInvariant_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
-- given
  (h : IsErgodic (G := G) μ) :
-- imply
  IsTranslationInvariant (G := G) μ := by
-- proof
  apply StatMech.ConfigSpace.IsErgodic.isTranslationInvariant h

/--
[IsTranslationInvariant.map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma map_eq_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {g : G}
-- given
  (h : IsTranslationInvariant (G := G) μ) :
-- imply
  Measure.map (shift g : ConfigSpace E → ConfigSpace E) μ = μ := by
-- proof
  apply StatMech.ConfigSpace.IsTranslationInvariant.map_eq h g

/--
[IsTranslationInvariant.measure_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean)
-/
@[path]
private lemma measure_preimage_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {g : G}
  {s : Set (ConfigSpace E)}
-- given
  (h : IsTranslationInvariant (G := G) μ)
  (hs : MeasurableSet s) :
-- imply
  μ ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s) = μ s := by
-- proof
  apply StatMech.ConfigSpace.IsTranslationInvariant.measure_preimage h g hs


-- created on 2026-10-23

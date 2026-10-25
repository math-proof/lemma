import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.SelfDualDichotomy
open MeasureTheory Set Filter Topology SimpleGraph StatMech StatMech.TwoDim


/--
[kdi_measurable_rotConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_measurable_rotConfig_eq :
-- imply
  Measurable kdi_rotConfig := by
-- proof
  apply StatMech.TwoDim.kdi_measurable_rotConfig

/--
[kdi_map_rotConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_map_rotConfig_eq :
-- imply
  Measure.map kdi_rotConfig halfMeasure = halfMeasure := by
-- proof
  apply StatMech.TwoDim.kdi_map_rotConfig

/--
[kdi_rotConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_rotConfig_measurePreserving_eq :
-- imply
  MeasurePreserving kdi_rotConfig halfMeasure halfMeasure := by
-- proof
  apply StatMech.TwoDim.kdi_rotConfig_measurePreserving

/--
[kdi_selfDualRotation_preserves_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_selfDualRotation_preserves_half_eq
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure) :
-- imply
  Measure.map (R ∘ dualConfig) halfMeasure = halfMeasure := by
-- proof
  apply StatMech.TwoDim.kdi_selfDualRotation_preserves_half R hRmeas hRpres

/--
[kdi_selfDual_crossing_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_selfDual_crossing_half_eq
  {H : Set (ConfigSpace (Sym2 (Site 2)))}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hHm : MeasurableSet H)
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : Hᶜ = (R ∘ dualConfig) ⁻¹' H) :
-- imply
  halfMeasure.real H = 1 / 2 := by
-- proof
  apply StatMech.TwoDim.kdi_selfDual_crossing_half hHm hRmeas hRpres hdich

/--
[kdi_crossing_balance_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_crossing_balance_family_eq
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
  {R : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))}
-- given
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hRmeas : Measurable R)
  (hRpres : Measure.map R halfMeasure = halfMeasure)
  (hdich : ∀ n, (boxFam n)ᶜ = (R ∘ dualConfig) ⁻¹' (boxFam n)) :
-- imply
  ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := by
-- proof
  apply StatMech.TwoDim.kdi_crossing_balance_family hHm hRmeas hRpres hdich

/--
[kdi_crossingPair_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_crossingPair_incompatible_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
-- proof
  apply StatMech.TwoDim.kdi_crossingPair_incompatible ω e

/--
[kdi_blocking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_blocking_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
  {x' y' : Site 2}
  {w' : (openSubgraph 2 (dualConfig ω)).Walk x' y'}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ w.edges)
  (he' : crossEdge e ∈ w'.edges) :
-- imply
  False := by
-- proof
  apply StatMech.TwoDim.kdi_blocking ω w w' e he he'

/--
[kdi_selfDual_crossing_half_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_selfDual_crossing_half_rot_eq
  {H : Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hHm : MeasurableSet H)
  (hdich : Hᶜ = (kdi_rotConfig ∘ dualConfig) ⁻¹' H) :
-- imply
  halfMeasure.real H = 1 / 2 := by
-- proof
  apply StatMech.TwoDim.kdi_selfDual_crossing_half_rot hHm hdich

/--
[kdi_crossing_balance_family_rot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/SelfDualDichotomy.lean)
-/
@[path]
private lemma kdi_crossing_balance_family_rot_eq
  {boxFam : ℕ → Set (ConfigSpace (Sym2 (Site 2)))}
-- given
  (hHm : ∀ n, MeasurableSet (boxFam n))
  (hdich : ∀ n, (boxFam n)ᶜ = (kdi_rotConfig ∘ dualConfig) ⁻¹' (boxFam n)) :
-- imply
  ∀ n : ℕ, halfMeasure.real (boxFam n) = 1 / 2 := by
-- proof
  apply StatMech.TwoDim.kdi_crossing_balance_family_rot hHm hdich


-- created on 2026-10-23

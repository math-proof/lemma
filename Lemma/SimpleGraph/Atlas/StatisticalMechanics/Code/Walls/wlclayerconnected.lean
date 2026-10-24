import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wlclayerconnected
open SimpleGraph Function StatMech StatMech.Wots


/--
[wlc_layerCell_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_layerCell_val_eq
  {K : Set (Site 2)}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (wlc_layerCell K d).1 = d.1.head := by
-- proof
  apply StatMech.Wots.wlc_layerCell_val K d

/--
[wlc_layerReachable_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_layerReachable_step_eq
  {K : Set (Site 2)}
  {d : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (wdc_layerGraph K).Reachable (wlc_layerCell K d) (wlc_layerCell K (dartNextSub K d)) := by
-- proof
  apply StatMech.Wots.wlc_layerReachable_step K d

/--
[wlc_layerReachable_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_layerReachable_of_sameOrbit_eq
  {K : Set (Site 2)}
  {d1 d2 : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : SameOrbit K d1.1 d2.1) :
-- imply
  (wdc_layerGraph K).Reachable (wlc_layerCell K d1) (wlc_layerCell K d2) := by
-- proof
  apply StatMech.Wots.wlc_layerReachable_of_sameOrbit K h

/--
[wlc_layerConnected_of_orbitTraceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_layerConnected_of_orbitTraceSurjective_eq
  {K : Set (Site 2)}
-- given
  (hOTS : OrbitTraceSurjective K) :
-- imply
  wdc_LayerConnected K := by
-- proof
  apply StatMech.Wots.wlc_layerConnected_of_orbitTraceSurjective K hOTS

/--
[wlc_dartConnected_of_orbitTraceSurjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_dartConnected_of_orbitTraceSurjective_eq
  {K : Set (Site 2)}
-- given
  (hOTS : OrbitTraceSurjective K) :
-- imply
  wots_DartConnected K := by
-- proof
  apply StatMech.Wots.wlc_dartConnected_of_orbitTraceSurjective K hOTS

/--
[wlc_orbitTraceSurjective_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_orbitTraceSurjective_iff_eq
  {K : Set (Site 2)} :
-- imply
  OrbitTraceSurjective K ↔ (wots_LocalStepSameOrbit K ∧ wdc_LayerConnected K) := by
-- proof
  apply StatMech.Wots.wlc_orbitTraceSurjective_iff K

/--
[wlc_layerConnected_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wlclayerconnected.lean)
-/
@[path]
private lemma wlc_layerConnected_singleton_eq
  {c : Site 2} :
-- imply
  wdc_LayerConnected ({c} : Set (Site 2)) := by
-- proof
  apply StatMech.Wots.wlc_layerConnected_singleton c


-- created on 2026-10-23

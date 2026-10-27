import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[realisedContourWalkEncoding_of_perContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma realisedContourWalkEncoding_of_perContour_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : PerContourDualCircuit d n ℓ) :
-- imply
  RealisedContourWalkEncoding d n ℓ := by
-- proof
  apply StatMech.Lattice.realisedContourWalkEncoding_of_perContour h

/--
[axisVertex_zero_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma axisVertex_zero_coord_eq
  {d : ℕ}
  {d j : ℕ}
-- given
  (h : 0 < d) :
-- imply
  axisVertex d j ⟨0, h⟩ = (j : ℤ) := by
-- proof
  apply StatMech.Lattice.axisVertex_zero_coord d j h

/--
[axisAnchorPool_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma axisAnchorPool_card_le_eq
  {d : ℕ}
  {d ℓ : ℕ} :
-- imply
  (axisAnchorPool d ℓ).card ≤ ℓ := by
-- proof
  apply StatMech.Lattice.axisAnchorPool_card_le d ℓ

/--
[axisVertex_zero_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma axisVertex_zero_eq_origin_eq
  {d : ℕ} :
-- imply
  axisVertex d 0 = StatMech.Ising.origin d := by
-- proof
  apply StatMech.Lattice.axisVertex_zero_eq_origin

/--
[perContourDualCircuit_of_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma perContourDualCircuit_of_axis_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : AxisContourDualCircuit d n ℓ) :
-- imply
  PerContourDualCircuit d n ℓ := by
-- proof
  apply StatMech.Lattice.perContourDualCircuit_of_axis h

/--
[realisedContourWalkEncoding_of_axisCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma realisedContourWalkEncoding_of_axisCircuit_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : AxisContourDualCircuit d n ℓ) :
-- imply
  RealisedContourWalkEncoding d n ℓ := by
-- proof
  apply StatMech.Lattice.realisedContourWalkEncoding_of_axisCircuit h

/--
[perContourDualCircuit_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma perContourDualCircuit_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  PerContourDualCircuit d n ℓ := by
-- proof
  apply StatMech.Lattice.perContourDualCircuit_of_empty hempty

/--
[axisContourDualCircuit_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma axisContourDualCircuit_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  AxisContourDualCircuit d n ℓ := by
-- proof
  apply StatMech.Lattice.axisContourDualCircuit_of_empty hempty

/--
[contourSubsetCountBound_of_empty_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_empty_axis_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_empty_axis hempty


-- created on 2026-10-23

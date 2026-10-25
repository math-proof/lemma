import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[realisedContours_card_le_of_walkEncoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma realisedContours_card_le_of_walkEncoding_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : RealisedContourWalkEncoding d n ℓ) :
-- imply
  (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.realisedContours_card_le_of_walkEncoding h

/--
[contourSubsetCountBound_of_walkEncoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_walkEncoding_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : RealisedContourWalkEncoding d n ℓ) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_walkEncoding h

/--
[connFamily_fixedLen_card_le_peierls_of_walkEncoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_le_peierls_of_walkEncoding_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : RealisedContourWalkEncoding d n ℓ) :
-- imply
  ((connClusterFamily (d := d) n).filter (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_le_peierls_of_walkEncoding h

/--
[connClusterFamily_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma connClusterFamily_nonempty_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  ({StatMech.Ising.origin d} : Finset (Site d)) ∈ connClusterFamily (d := d) n := by
-- proof
  apply StatMech.Lattice.connClusterFamily_nonempty n

/--
[realisedContourWalkEncoding_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma realisedContourWalkEncoding_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  RealisedContourWalkEncoding d n ℓ := by
-- proof
  apply StatMech.Lattice.realisedContourWalkEncoding_of_empty hempty

/--
[contourSubsetCountBound_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_empty hempty

/--
[connectedContourCount_of_walkEncoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma connectedContourCount_of_walkEncoding_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ∀ ℓ, RealisedContourWalkEncoding d n ℓ) :
-- imply
  StatMech.Ising.ConnectedContourCount d n := by
-- proof
  apply StatMech.Lattice.connectedContourCount_of_walkEncoding h

/--
[peierls_long_range_order_of_walkEncoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean)
-/
@[path]
private lemma peierls_long_range_order_of_walkEncoding_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (h : ∀ (n ℓ : ℕ), RealisedContourWalkEncoding d n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → StatMech.Ising.plusMeasure d n β 0 ≠ StatMech.Ising.minusMeasure d n β 0 := by
-- proof
  apply StatMech.Lattice.peierls_long_range_order_of_walkEncoding hd h


-- created on 2026-10-23

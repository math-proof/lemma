import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.ContourCount
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[card_walkEdgeSets_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma card_walkEdgeSets_le_eq
  {G : SimpleGraph V}
  [DecidableEq V]
  [SimpleGraph.LocallyFinite G]
  {D : ℕ}
  {B : Finset V}
  {ℓ : ℕ}
-- given
  (hD : ∀ v, G.degree v ≤ D) :
-- imply
  (walkEdgeSets G B ℓ).card ≤ B.card * D ^ ℓ := by
-- proof
  apply StatMech.Lattice.card_walkEdgeSets_le G hD B ℓ

/--
[card_walkEdgeSets_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma card_walkEdgeSets_le_pow_eq
  {d : ℕ}
  {B : Finset (Site d)}
  {ℓ : ℕ} :
-- imply
  (walkEdgeSets (hypercubicLattice d) B ℓ).card ≤ B.card * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.card_walkEdgeSets_le_pow B ℓ

/--
[realisedContours_card_le_of_walkRealisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma realisedContours_card_le_of_walkRealisation_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : ContourWalkRealisation d n ℓ) :
-- imply
  (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.realisedContours_card_le_of_walkRealisation h

/--
[contourSubsetCountBound_of_walkRealisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_walkRealisation_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : ContourWalkRealisation d n ℓ) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_walkRealisation h

/--
[connectedContourCount_of_walkRealisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma connectedContourCount_of_walkRealisation_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ∀ ℓ, ContourWalkRealisation d n ℓ) :
-- imply
  ConnectedContourCount d n := by
-- proof
  apply StatMech.Lattice.connectedContourCount_of_walkRealisation h

/--
[contourLen_pos_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma contourLen_pos_of_nonempty_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)}
-- given
  (hd : 1 ≤ d)
  (hKbox : (↑K : Set (Site d)) ⊆ box d n)
  (hne : K.Nonempty) :
-- imply
  0 < contourLen (↑K : Set (Site d)) (bondFinsetTouch d n) := by
-- proof
  apply StatMech.Lattice.contourLen_pos_of_nonempty hd hKbox hne

/--
[realisedContours_zero_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma realisedContours_zero_eq_empty_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  realisedContours d n 0 = ∅ := by
-- proof
  apply StatMech.Lattice.realisedContours_zero_eq_empty hd n

/--
[contourWalkRealisation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma contourWalkRealisation_zero_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ContourWalkRealisation d n 0 := by
-- proof
  apply StatMech.Lattice.contourWalkRealisation_zero hd n

/--
[connectedContourCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma connectedContourCount_zero_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (((connClusterFamily (d := d) n).filter (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = 0)).card : ℝ) ≤ (0 : ℝ) * (2 * d : ℝ) ^ 0 := by
-- proof
  apply StatMech.Lattice.connectedContourCount_zero hd n

/--
[contourWalkRealisation_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma contourWalkRealisation_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  ContourWalkRealisation d n ℓ := by
-- proof
  apply StatMech.Lattice.contourWalkRealisation_of_empty hempty

/--
[singleton_origin_mem_realisedContours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/ContourCount.lean)
-/
@[path]
private lemma singleton_origin_mem_realisedContours_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  crossEdges (↑({origin d} : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n) ∈ realisedContours d n (contourLen (↑({origin d} : Finset (Site d)) : Set (Site d)) (bondFinsetTouch d n)) := by
-- proof
  apply StatMech.Lattice.singleton_origin_mem_realisedContours n


-- created on 2026-10-23

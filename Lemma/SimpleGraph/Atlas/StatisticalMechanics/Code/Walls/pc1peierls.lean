import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.pc1peierls.Part2
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[pc1_axisWalks_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_axisWalks_card_le_eq
  {d : ℕ}
  {d ℓ : ℕ} :
-- imply
  (pc1_axisWalks d ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.pc1_axisWalks_card_le d ℓ

/--
[pc1_realisedContours_card_le_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_realisedContours_card_le_of_injection_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : pc1_ContourInjection d n ℓ) :
-- imply
  (realisedContours d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.pc1_realisedContours_card_le_of_injection h

/--
[pc1_contourSubsetCountBound_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_contourSubsetCountBound_of_injection_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : pc1_ContourInjection d n ℓ) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_contourSubsetCountBound_of_injection h

/--
[pc1_mem_axisAnchorPool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_mem_axisAnchorPool_eq
  {d : ℕ}
  {ℓ : ℕ}
  {v : Site d}
-- given
  (hv : v ∈ axisAnchorPool d ℓ) :
-- imply
  ∃ j : ℕ, j < ℓ ∧ v = axisVertex d j := by
-- proof
  apply StatMech.Lattice.pc1_mem_axisAnchorPool hv

/--
[pc1_injection_of_axisCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_injection_of_axisCircuit_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : AxisContourDualCircuit d n ℓ) :
-- imply
  pc1_ContourInjection d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_injection_of_axisCircuit h

/--
[pc1_axisCircuit_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_axisCircuit_of_injection_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : pc1_ContourInjection d n ℓ) :
-- imply
  AxisContourDualCircuit d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_axisCircuit_of_injection h

/--
[pc1_axisContourDualCircuit_iff_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_axisContourDualCircuit_iff_injection_eq
  {d : ℕ}
  {n ℓ : ℕ} :
-- imply
  AxisContourDualCircuit d n ℓ ↔ pc1_ContourInjection d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_axisContourDualCircuit_iff_injection

/--
[pc1_connectedContourCount_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_connectedContourCount_of_injection_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ∀ ℓ, pc1_ContourInjection d n ℓ) :
-- imply
  ConnectedContourCount d n := by
-- proof
  apply StatMech.Lattice.pc1_connectedContourCount_of_injection h

/--
[pc1_peierls_long_range_order_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_peierls_long_range_order_of_injection_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (h : ∀ (n ℓ : ℕ), pc1_ContourInjection d n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → StatMech.Ising.plusMeasure d n β 0 ≠ StatMech.Ising.minusMeasure d n β 0 := by
-- proof
  apply StatMech.Lattice.pc1_peierls_long_range_order_of_injection hd h

/--
[pc1_contourInjection_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_contourInjection_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  pc1_ContourInjection d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_contourInjection_of_empty hempty

/--
[pc1_contourSubsetCountBound_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_contourSubsetCountBound_of_empty_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours d n ℓ = ∅) :
-- imply
  ContourSubsetCountBound d n ℓ := by
-- proof
  apply StatMech.Lattice.pc1_contourSubsetCountBound_of_empty hempty

/--
[pc1_axisWalks_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean)
-/
@[path]
private lemma pc1_axisWalks_nonempty_eq
  {d : ℕ}
  {k : ℕ}
-- given
  (hd : 1 ≤ d)
  (hk : 1 ≤ k) :
-- imply
  (pc1_axisWalks d (2 * k)).Nonempty := by
-- proof
  apply StatMech.Lattice.pc1_axisWalks_nonempty hd hk


-- created on 2026-10-23

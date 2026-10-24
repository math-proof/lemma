import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc105contraction
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc105_boxes_overlap_of_close_centres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_boxes_overlap_of_close_centres_eq
  {d : ℕ}
  {L : ℕ}
  {y z : Site d}
-- given
  (hyz : (y - z) ∈ box d L) :
-- imply
  z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z := by
-- proof
  apply StatMech.Walls.bc105_boxes_overlap_of_close_centres hyz

/--
[bc105_centre_mem_own_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_centre_mem_own_box_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site d} :
-- imply
  z ∈ bc61_boxAround d L z := by
-- proof
  apply StatMech.Walls.bc105_centre_mem_own_box L z

/--
[bc105_boxes_overlap_of_adjacent_centres](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_boxes_overlap_of_adjacent_centres_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site d}
-- given
  (hL : 1 ≤ L)
  (hd : 1 ≤ d) :
-- imply
  ∃ y : Site d, y ≠ z ∧ z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z ∧ y ∈ bc61_boxAround d L y ∧ y ∈ bc61_boxAround d L z := by
-- proof
  apply StatMech.Walls.bc105_boxes_overlap_of_adjacent_centres hL hd z

/--
[bc105_contractedTrifGraph_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_contractedTrifGraph_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc103_ContractedTrifGraph ω L R := by
-- proof
  apply StatMech.Walls.bc105_contractedTrifGraph_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc105_count_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_count_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc105_count_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc105_adversary_has_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_adversary_has_trif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc105_adversary_has_trif hL

/--
[bc105_adversary_box_overlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_adversary_box_overlap_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site 2}
-- given
  (hz : (z : Site 2) ∈ box 2 L) :
-- imply
  (0 : Site 2) ∈ bc61_boxAround 2 L 0 ∧ z ∈ bc61_boxAround 2 L 0 ∧ z ∈ bc61_boxAround 2 L z := by
-- proof
  apply StatMech.Walls.bc105_adversary_box_overlap hz

/--
[bc105_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc105contraction.lean)
-/
@[path]
private lemma bc105_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc103_ContractedTrifGraph ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) ∧ (∀ (L : ℕ) (y z : Site d), (y - z) ∈ box d L → z ∈ bc61_boxAround d L y ∧ z ∈ bc61_boxAround d L z) ∧ (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc105_status


-- created on 2026-10-23

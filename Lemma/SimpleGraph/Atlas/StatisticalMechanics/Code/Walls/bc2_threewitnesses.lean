import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc2_threewitnesses
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc2_threeWitnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_threeWitnesses_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc2_ThreeWitnesses d n := by
-- proof
  apply StatMech.Walls.bc2_threeWitnesses n

/--
[bc2_disjoint_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_disjoint_of_ne_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : cluster d ω x ≠ cluster d ω y) :
-- imply
  Disjoint (cluster d ω x) (cluster d ω y) := by
-- proof
  apply StatMech.Walls.bc2_disjoint_of_ne h

/--
[bc2_threeWitnesses_pairwise_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_threeWitnesses_pairwise_disjoint_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧ (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧ Disjoint (cluster d ω x₁) (cluster d ω x₂) ∧ Disjoint (cluster d ω x₁) (cluster d ω x₃) ∧ Disjoint (cluster d ω x₂) (cluster d ω x₃) := by
-- proof
  apply StatMech.Walls.bc2_threeWitnesses_pairwise_disjoint n ω hω

/--
[bc2_distinct_sites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_distinct_sites_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧ (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
-- proof
  apply StatMech.Walls.bc2_distinct_sites n ω hω

/--
[bc2_threeMeetBox_numInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_threeMeetBox_numInfinite_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  numInfiniteClusters d ω = ⊤ := by
-- proof
  apply StatMech.Walls.bc2_threeMeetBox_numInfinite n ω hω

/--
[bc2_three_witnesses_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_threewitnesses.lean)
-/
@[path]
private lemma bc2_three_witnesses_node_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc2_ThreeWitnesses d n ∧ (∀ ω ∈ threeMeetBox d n, ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧ (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧ Disjoint (cluster d ω x₁) (cluster d ω x₂) ∧ Disjoint (cluster d ω x₁) (cluster d ω x₃) ∧ Disjoint (cluster d ω x₂) (cluster d ω x₃)) := by
-- proof
  apply StatMech.Walls.bc2_three_witnesses_node n


-- created on 2026-10-23

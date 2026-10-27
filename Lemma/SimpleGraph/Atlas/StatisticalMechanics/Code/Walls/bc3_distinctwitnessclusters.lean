import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_distinctwitnessclusters.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace SimpleGraph StatMech.Percolation StatMech StatMech.Walls


/--
[bc3_cutClusterEq_of_originNotMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_cutClusterEq_of_originNotMem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω x) :
-- imply
  cluster d (removeSite 0 ω) x = cluster d ω x := by
-- proof
  apply StatMech.Walls.bc3_cutClusterEq_of_originNotMem ω x h0

/--
[bc3_cutClusterInfinite_of_originNotMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_cutClusterInfinite_of_originNotMem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d ω x).Infinite)
  (h0 : (0 : Site d) ∉ cluster d ω x) :
-- imply
  (cluster d (removeSite 0 ω) x).Infinite := by
-- proof
  apply StatMech.Walls.bc3_cutClusterInfinite_of_originNotMem ω x hinf h0

/--
[bc3_clusterEq_of_originMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_clusterEq_of_originMem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hx : (0 : Site d) ∈ cluster d ω x)
  (hy : (0 : Site d) ∈ cluster d ω y) :
-- imply
  cluster d ω x = cluster d ω y := by
-- proof
  apply StatMech.Walls.bc3_clusterEq_of_originMem ω hx hy

/--
[bc3_twoArms_avoid_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_twoArms_avoid_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
-- imply
  ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₂) ∨ ((0 : Site d) ∉ cluster d ω x₁ ∧ (0 : Site d) ∉ cluster d ω x₃) ∨ ((0 : Site d) ∉ cluster d ω x₂ ∧ (0 : Site d) ∉ cluster d ω x₃) := by
-- proof
  apply StatMech.Walls.bc3_twoArms_avoid_origin ω hd12 hd13 hd23

/--
[bc3_twoArms_cutInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_twoArms_cutInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite)
  (hd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
-- imply
  ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite) ∨ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∨ ((cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
-- proof
  apply StatMech.Walls.bc3_twoArms_cutInfinite ω hi1 hi2 hi3 hd12 hd13 hd23

/--
[bc3_arm_cutInfinite_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_arm_cutInfinite_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hres : bc3_OriginCutLeavesInfinite ω)
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ x', x' ∈ cluster d ω x ∧ (cluster d (removeSite 0 ω) x').Infinite := by
-- proof
  apply StatMech.Walls.bc3_arm_cutInfinite_of_residue ω hres x hinf

/--
[bc3_armEscapes_of_cutInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_armEscapes_of_cutInfinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x' : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x').Infinite) :
-- imply
  ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x' y ∧ (cluster d (removeSite 0 ω) y).Infinite ∧ y ≠ 0 := by
-- proof
  apply StatMech.Walls.bc3_armEscapes_of_cutInfinite ω x' hinf n

/--
[bc3_threeArms_cutInfinite_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_threeArms_cutInfinite_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hres : bc3_OriginCutLeavesInfinite ω)
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧ x₃' ∈ cluster d ω x₃ ∧ (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite := by
-- proof
  apply StatMech.Walls.bc3_threeArms_cutInfinite_of_residue ω hres hi1 hi2 hi3

/--
[bc3_distinctWitnessClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_distinctWitnessClusters_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hres : ∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) :
-- imply
  bc3_DistinctWitnessClusters d n := by
-- proof
  apply StatMech.Walls.bc3_distinctWitnessClusters n hres

/--
[bc3_distinctWitnessClusters_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_distinctWitnessClusters_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite)
  (h01 : (0 : Site d) ∉ cluster d ω x₁)
  (h02 : (0 : Site d) ∉ cluster d ω x₂)
  (h03 : (0 : Site d) ∉ cluster d ω x₃) :
-- imply
  (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite := by
-- proof
  apply StatMech.Walls.bc3_distinctWitnessClusters_nonvacuous ω hi1 hi2 hi3 h01 h02 h03

/--
[bc3_originCutLeavesInfinite_of_origin_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_originCutLeavesInfinite_of_origin_isolated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hnone : ∀ x, (cluster d ω x).Infinite → (0 : Site d) ∉ cluster d ω x) :
-- imply
  bc3_OriginCutLeavesInfinite ω := by
-- proof
  apply StatMech.Walls.bc3_originCutLeavesInfinite_of_origin_isolated ω hnone

/--
[bc3_distinctWitnessClusters_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_distinctwitnessclusters.lean)
-/
@[path]
private lemma bc3_distinctWitnessClusters_node_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  ((∀ ω ∈ threeMeetBox d n, bc3_OriginCutLeavesInfinite ω) → bc3_DistinctWitnessClusters d n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) {x₁ x₂ x₃ : Site d}, (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite → cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ → cluster d ω x₂ ≠ cluster d ω x₃ → ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite) ∨ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∨ ((cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)) := by
-- proof
  apply StatMech.Walls.bc3_distinctWitnessClusters_node n


-- created on 2026-10-23

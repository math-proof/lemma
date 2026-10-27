import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters.Part2
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc7_cutCluster_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7distinctwitnessclusters.lean)
-/
@[path]
private lemma bc7_cutCluster_ne_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₁' x₂' : Site d}
-- given
  (hx₁' : x₁' ∈ cluster d ω x₁)
  (hx₂' : x₂' ∈ cluster d ω x₂)
  (hne : cluster d ω x₁ ≠ cluster d ω x₂) :
-- imply
  cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' := by
-- proof
  apply StatMech.Walls.bc7_cutCluster_ne ω hx₁' hx₂' hne

/--
[bc7_threeArms_cutInfinite_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7distinctwitnessclusters.lean)
-/
@[path]
private lemma bc7_threeArms_cutInfinite_distinct_eq
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
  ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧ x₃' ∈ cluster d ω x₃ ∧ (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧ cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧ cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
-- proof
  apply StatMech.Walls.bc7_threeArms_cutInfinite_distinct ω hi1 hi2 hi3 hd12 hd13 hd23

/--
[bc7_distinctWitnessClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7distinctwitnessclusters.lean)
-/
@[path]
private lemma bc7_distinctWitnessClusters_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc7_DistinctWitnessClusters d n := by
-- proof
  apply StatMech.Walls.bc7_distinctWitnessClusters n


-- created on 2026-10-23

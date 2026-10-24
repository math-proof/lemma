import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.AvoidingRoutingResidue
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[arr_cluster_removeSite_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_cluster_removeSite_origin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cluster d (removeSite 0 ω) (0 : Site d) = {(0 : Site d)} := by
-- proof
  apply StatMech.Percolation.arr_cluster_removeSite_origin ω

/--
[arr_cluster_removeSite_origin_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_cluster_removeSite_origin_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (cluster d (removeSite 0 ω) (0 : Site d)).Finite := by
-- proof
  apply StatMech.Percolation.arr_cluster_removeSite_origin_finite ω

/--
[arr_witness_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_witness_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  x ≠ 0 := by
-- proof
  apply StatMech.Percolation.arr_witness_ne_zero ω hinf

/--
[arr_routingResidue_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_routingResidue_of_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a)
  (hc : Connected d (removeSite 0 ω) a x)
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ava_AvoidingRoutingResidue ω x := by
-- proof
  apply StatMech.Percolation.arr_routingResidue_of_reach ω hadj hc hinf

/--
[arr_avoidingAttachment_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_avoidingAttachment_of_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a)
  (hc : Connected d (removeSite 0 ω) a x)
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.arr_avoidingAttachment_of_reach ω hadj hc hinf

/--
[arr_three_residues_of_reachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_three_residues_of_reachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
-- proof
  apply StatMech.Percolation.arr_three_residues_of_reachOrigin ω h

/--
[arr_three_avoidingAttachment_of_reachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_three_avoidingAttachment_of_reachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  ∃ x₁ x₂ x₃ : Site d, cla_AvoidingAttachment ω x₁ ∧ cla_AvoidingAttachment ω x₂ ∧ cla_AvoidingAttachment ω x₃ := by
-- proof
  apply StatMech.Percolation.arr_three_avoidingAttachment_of_reachOrigin ω h

/--
[arr_boxAvoidingRoutingResidue_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_boxAvoidingRoutingResidue_of_reach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hreach : ∀ ω ∈ threeMeetBox d n, mco_ThreeClustersReachOrigin ω) :
-- imply
  ∀ ω ∈ threeMeetBox d n, ∃ x₁ x₂ x₃ : Site d, ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
-- proof
  apply StatMech.Percolation.arr_boxAvoidingRoutingResidue_of_reach hreach

/--
[arr_routingResidue_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_routingResidue_satisfiable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ava_AvoidingRoutingResidue ω x := by
-- proof
  apply StatMech.Percolation.arr_routingResidue_satisfiable ω x hadj hinf

/--
[arr_three_residues_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingRoutingResidue.lean)
-/
@[path]
private lemma arr_three_residues_satisfiable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (h0 : (hypercubicLattice d).Adj 0 x₁)
  (h1 : (hypercubicLattice d).Adj 0 x₂)
  (h2 : (hypercubicLattice d).Adj 0 x₃)
  (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
-- proof
  apply StatMech.Percolation.arr_three_residues_satisfiable ω x₁ x₂ x₃ h0 h1 h2 hi1 hi2 hi3


-- created on 2026-10-23

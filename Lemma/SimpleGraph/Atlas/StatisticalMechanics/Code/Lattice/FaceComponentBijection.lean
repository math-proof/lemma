import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[fcb_offComplGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offComplGraph_adj_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (x y : {z : Site 2 // z ∉ Vc.support}) :
-- imply
  (fcb_offComplGraph Vc).Adj x y ↔ (ffc_offSupportLattice {z | z ∈ Vc.support}).Adj (x : Site 2) (y : Site 2) := by
-- proof
  apply StatMech.Lattice.fcb_offComplGraph_adj Vc x y

/--
[fcb_induce_reachable_to_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_induce_reachable_to_ambient_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (fcb_offComplGraph Vc).Reachable x y) :
-- imply
  (ffc_offSupportLattice {z | z ∈ Vc.support}).Reachable (x : Site 2) (y : Site 2) := by
-- proof
  apply StatMech.Lattice.fcb_induce_reachable_to_ambient Vc h

/--
[fcb_ambient_reachable_to_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_ambient_reachable_to_induce_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (ffc_offSupportLattice {z | z ∈ Vc.support}).Reachable (x : Site 2) (y : Site 2)) :
-- imply
  (fcb_offComplGraph Vc).Reachable x y := by
-- proof
  apply StatMech.Lattice.fcb_ambient_reachable_to_induce Vc h

/--
[fcb_induce_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_induce_reachable_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}} :
-- imply
  (fcb_offComplGraph Vc).Reachable x y ↔ ∃ p : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.fcb_induce_reachable_iff Vc

/--
[fcb_offCompl_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offCompl_sameSide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : {z : Site 2 // z ∉ Vc.support}}
-- given
  (h : (fcb_offComplGraph Vc).Reachable x y) :
-- imply
  ((x : Site 2) ∈ jec_leftRegion Vc ↔ (y : Site 2) ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.fcb_offCompl_sameSide Vc h

/--
[fcb_two_components_of_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_two_components_of_sides_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.fcb_two_components_of_sides Vc hxin hxoff hyout hyoff hin hout

/--
[fcb_offComplComponentCount_eq_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offComplComponentCount_eq_faceCount_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
  {x y : Site 2}
-- given
  (hc : c.IsCycle)
  (hxin : x ∈ jec_leftRegion Vc)
  (hxoff : x ∉ Vc.support)
  (hyout : y ∉ jec_leftRegion Vc)
  (hyoff : y ∉ Vc.support)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
-- proof
  apply StatMech.Lattice.fcb_offComplComponentCount_eq_faceCount Vc c hc hxin hxoff hyout hyoff hin hout

/--
[fcb_inside_conn_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_inside_conn_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sIn : Site 2}
-- given
  (hoff : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn) :
-- imply
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.fcb_inside_conn_of_covers Vc hoff hcovIn

/--
[fcb_outside_conn_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_outside_conn_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {sOut : Site 2}
-- given
  (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
-- imply
  ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → s ∉ Vc.support → t ∉ Vc.support → ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.fcb_outside_conn_of_covers Vc hcovOut

/--
[fcb_offComplComponentCount_eq_two_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offComplComponentCount_eq_two_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {sIn sOut : Site 2}
-- given
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hxin : x ∈ jec_leftRegion Vc)
  (hyout : y ∉ jec_leftRegion Vc)
  (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
  (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.fcb_offComplComponentCount_eq_two_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut

/--
[fcb_offComplJordanRegion_of_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offComplJordanRegion_of_covers_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {sIn sOut : Site 2}
-- given
  (hoffIn : ∀ s ∈ jec_leftRegion Vc, s ∉ Vc.support)
  (hoffOut : ∀ s ∉ jec_leftRegion Vc, s ∉ Vc.support)
  (hxin : x ∈ jec_leftRegion Vc)
  (hyout : y ∉ jec_leftRegion Vc)
  (hcovIn : jec_leftRegion Vc ⊆ offSupportComponent Vc sIn)
  (hcovOut : (jec_leftRegion Vc)ᶜ ⊆ offSupportComponent Vc sOut) :
-- imply
  fcb_OffComplJordanRegion Vc := by
-- proof
  apply StatMech.Lattice.fcb_offComplJordanRegion_of_covers Vc hoffIn hoffOut hxin hyout hcovIn hcovOut

/--
[fcb_two_components_of_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_two_components_of_region_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : fcb_OffComplJordanRegion Vc) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.fcb_two_components_of_region Vc h

/--
[fcb_offComplComponentCount_eq_faceCount_of_jordanRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_offComplComponentCount_eq_faceCount_of_jordanRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {G : SimpleGraph V}
  {v : V}
  {c : G.Walk v v}
-- given
  (h : fcb_OffComplJordanRegion Vc)
  (hc : c.IsCycle) :
-- imply
  Nat.card (fcb_offComplGraph Vc).ConnectedComponent = faceCount c.toSubgraph.coe := by
-- proof
  apply StatMech.Lattice.fcb_offComplComponentCount_eq_faceCount_of_jordanRegion Vc h c hc

/--
[fcb_self_component_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_self_component_side_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (v : {z : Site 2 // z ∉ Vc.support}) :
-- imply
  ((v : Site 2) ∈ jec_leftRegion Vc ↔ (v : Site 2) ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.fcb_self_component_side Vc v

/--
[fcb_adj_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceComponentBijection.lean)
-/
@[path]
private lemma fcb_adj_sameSide_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  (u ∈ jec_leftRegion Vc ↔ v ∈ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.fcb_adj_sameSide Vc hadj hu hv


-- created on 2026-10-23

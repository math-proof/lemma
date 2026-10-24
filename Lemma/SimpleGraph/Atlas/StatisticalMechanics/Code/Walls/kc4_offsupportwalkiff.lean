import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc4_offsupportwalkiff
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc4_notMem_supportSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_notMem_supportSet_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2} :
-- imply
  z ∉ oc_supportSet Vc ↔ z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_notMem_supportSet_iff Vc z

/--
[kc4_offSupportWalk_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_offSupportWalk_of_reachable_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support)
  (h : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_offSupportWalk_of_reachable Vc hx h

/--
[kc4_reachable_of_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_reachable_of_offSupportWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y := by
-- proof
  apply StatMech.Walls.kc4_reachable_of_offSupportWalk Vc p hp

/--
[kc4_reachable_iff_offSupportWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_reachable_iff_offSupportWalk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_reachable_iff_offSupportWalk Vc hx

/--
[kc4_offSupportWalk_endpoint_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_offSupportWalk_endpoint_offSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  x ∉ Vc.support ∧ y ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_offSupportWalk_endpoint_offSupport Vc p hp

/--
[kc4_reachable_offSupport_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_reachable_offSupport_symm_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∉ Vc.support) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x y ↔ y ∉ Vc.support ∧ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_reachable_offSupport_symm Vc hx

/--
[kc4_no_offSupportWalk_of_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_no_offSupportWalk_of_mem_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
-- given
  (hx : x ∈ Vc.support) :
-- imply
  ¬ ∃ p : (hypercubicLattice 2).Walk x y, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_no_offSupportWalk_of_mem_support Vc hx

/--
[kc4_offSupportWalk_iff_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_offSupportWalk_iff_sharp_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x : Site 2}
-- given
  (hx : x ∈ Vc.support) :
-- imply
  (ffc_offSupportLattice (oc_supportSet Vc)).Reachable x x ∧ ¬ ∃ p : (hypercubicLattice 2).Walk x x, ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_offSupportWalk_iff_sharp Vc hx

/--
[kc4_node_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_offsupportwalkiff.lean)
-/
@[path]
private lemma kc4_node_nonvacuous_eq
  {a : Site 2} :
-- imply
  let Vc : (hypercubicLattice 2).Walk (![5, 5] : Site 2) ![5, 5] := SimpleGraph.Walk.nil (ffc_offSupportLattice (oc_supportSet Vc)).Reachable (![0, 0] : Site 2) ![1, 0] ∧ ∃ p : (hypercubicLattice 2).Walk (![0, 0] : Site 2) ![1, 0], ∀ z ∈ p.support, z ∉ Vc.support := by
-- proof
  apply StatMech.Walls.kc4_node_nonvacuous


-- created on 2026-10-23

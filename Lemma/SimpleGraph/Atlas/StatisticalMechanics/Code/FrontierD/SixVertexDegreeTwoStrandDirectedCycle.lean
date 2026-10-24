import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandDirectedCycle
open StatMech StatMech.FrontierD


/--
[sixVertexDirectedTorusEdgeOfArrow_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_tail_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {edge : SixVertexTorusEdge T} :
-- imply
  (sixVertexDirectedTorusEdgeOfArrow omega edge).tail = (sixVertexTorusEdgeOutgoingDart omega edge).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_tail omega edge

/--
[sixVertexDirectedTorusEdgeOfArrow_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_head_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {edge : SixVertexTorusEdge T} :
-- imply
  (sixVertexDirectedTorusEdgeOfArrow omega edge).head = (sixVertexTorusDartBondMate T (sixVertexTorusEdgeOutgoingDart omega edge)).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_head omega edge

/--
[sixVertexDirectedTorusEdgeOfArrow_physical_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_physical_injective_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  Function.Injective (fun edge : SixVertexTorusEdge T => (sixVertexDirectedTorusEdgeOfArrow omega edge).physical) := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_physical_injective omega

/--
[sixVertexDegreeTwoLocalMate_incoming_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_incoming_false_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexLocalIncomingPattern omega (sixVertexDegreeTwoLocalMate hdegree dart.1).1.1 (sixVertexDegreeTwoLocalMate hdegree dart.1).1.2 = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_incoming_false homega heta hdegree dart

/--
[sixVertexDegreeTwoOrientedStrandEdge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedStrandEdge_tail_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).tail = dart.1.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedStrandEdge_tail homega heta hdegree dart

/--
[sixVertexDegreeTwoOrientedStrandEdge_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedStrandEdge_head_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).head = (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree dart).1.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedStrandEdge_head homega heta hdegree dart

/--
[sixVertexOrientedDisagreementDart_vertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexOrientedDisagreementDart_vertex_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Injective (fun dart : SixVertexOrientedDisagreementDart omega eta => dart.1.1.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexOrientedDisagreementDart_vertex_injective homega heta hdegree

/--
[sixVertexDegreeTwoOrientedStrandEdge_physical_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedStrandEdge_physical_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Injective (fun dart : SixVertexOrientedDisagreementDart omega eta => (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).physical) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedStrandEdge_physical_injective homega heta hdegree

/--
[permCycleFinEquivSupport_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma permCycleFinEquivSupport_succ_eq
  [Fintype D]
  [DecidableEq D]
  {cycle : Equiv.Perm D}
  {seed : cycle.support}
  {i : Fin (orderOf cycle)}
-- given
  (hcycle : cycle.IsCycle) :
-- imply
  permCycleFinEquivSupport cycle hcycle seed (finitePeriodicSucc (orderOf_pos cycle) i) = ⟨cycle (permCycleFinEquivSupport cycle hcycle seed i).1, Equiv.Perm.apply_mem_support.mpr (permCycleFinEquivSupport cycle hcycle seed i).2⟩ := by
-- proof
  apply StatMech.FrontierD.permCycleFinEquivSupport_succ cycle hcycle seed i

/--
[sixVertexDegreeTwoStrandCyclePerm_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCyclePerm_isCycle_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed).IsCycle := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCyclePerm_isCycle homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandCyclePerm_seed_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCyclePerm_seed_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  seed ∈ (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed).support := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCyclePerm_seed_mem homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandCycleEnumeration_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Injective (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_injective homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandCycleEnumeration_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_sameCycle_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle seed (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_sameCycle homega heta hdegree seed i

/--
[sixVertexDegreeTwoStrandCycleEnumeration_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandDirectedCycle.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_next_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed (finitePeriodicSucc (orderOf_pos (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed)) i) = sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_next homega heta hdegree seed i


-- created on 2026-10-23

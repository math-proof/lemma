import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConcreteRibbon.Part3
open Equiv Finset StatMech StatMech.FrontierD


/--
[fkMedialBlackDartSwap_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_vertex_eq
  {T : EvenTorus}
  {v : T.Vertex}
  {d : FKMedialBlackDart T} :
-- imply
  ((fkMedialBlackDartSwap v d).1).1 = d.1.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_vertex v d

/--
[fkMedialBlackDartSwap_apply_of_vertex_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_apply_of_vertex_ne_eq
  {T : EvenTorus}
  {v : T.Vertex}
  {d : FKMedialBlackDart T}
-- given
  (hd : d.1.1 ≠ v) :
-- imply
  fkMedialBlackDartSwap v d = d := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_apply_of_vertex_ne v d hd

/--
[fkMedialBlackDartSwap_commute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_commute_eq
  {T : EvenTorus}
  {v w : T.Vertex}
-- given
  (hvw : v ≠ w) :
-- imply
  Commute (fkMedialBlackDartSwap v) (fkMedialBlackDartSwap w) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_commute hvw

/--
[ribbonBoundaryPerm_insert_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma ribbonBoundaryPerm_insert_right_eq
  {T : EvenTorus}
  [DecidableEq E]
  [Fintype D]
  [DecidableEq D]
  {S : RibbonPermutationSystem E D}
  {F : Finset E}
  {e : E}
-- given
  (he : e ∉ F) :
-- imply
  S.boundaryPerm (insert e F) = S.boundaryPerm F * S.edgeFlip e := by
-- proof
  apply StatMech.FrontierD.ribbonBoundaryPerm_insert_right S F e he

/--
[fkRectRibbonSystem_boundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkRectRibbonSystem_boundaryPerm_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  (fkRectRibbonSystem R).boundaryPerm F = fkMedialBlackBoundaryPerm (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSystem_boundaryPerm R F

/--
[fkRectRibbonSystem_boundaryComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkRectRibbonSystem_boundaryComponents_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  (fkRectRibbonSystem R).boundaryComponents F = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonSystem_boundaryComponents R F

/--
[fkRectEulerHomologyDefect_classified_of_concreteRibbon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConcreteRibbon.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_classified_of_concreteRibbon_eq
  {T : EvenTorus}
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_classified_of_concreteRibbon R F


-- created on 2026-10-23

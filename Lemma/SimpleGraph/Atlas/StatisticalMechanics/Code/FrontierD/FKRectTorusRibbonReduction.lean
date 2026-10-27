import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonReduction
open Finset StatMech StatMech.FrontierD


/--
[fkRectEulerHomologyDefect_configurationOfEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonReduction.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_configurationOfEdges_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 * (fkRectFinsetClusterCount R F : Int) + (F.card : Int) - (fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F) : Int) - (Fintype.card R.Vertex : Nat) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_configurationOfEdges R F

/--
[fkRectEulerHomologyDefect_classified_of_ribbon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonReduction.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_classified_of_ribbon_eq
  {R : FKRectTorus}
  [Fintype D]
  [DecidableEq D]
  {S : RibbonPermutationSystem R.EdgeIndex D}
  {C : CellularRibbonDualData S}
  {F : Finset R.EdgeIndex}
-- given
  (hprimal : C.primalVertexCount = Fintype.card R.Vertex)
  (hgenus : C.genus = 1)
  (hboundary : ∀ F : Finset R.EdgeIndex, S.boundaryComponents F = fkRectMedialLoopCount R (fkRectConfigurationOfEdges R F))
  (hfullBoundary : S.boundaryComponents Finset.univ = C.dualVertexCount)
  (hmono : ∀ (F : Finset R.EdgeIndex) (e : R.EdgeIndex), e ∉ F → genusOneRibbonEulerDefect S C.primalVertexCount (fkRectFinsetClusterCount R) F ≤ genusOneRibbonEulerDefect S C.primalVertexCount (fkRectFinsetClusterCount R) (insert e F)) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_classified_of_ribbon R S C hprimal hgenus hboundary hfullBoundary hmono F


-- created on 2026-10-23

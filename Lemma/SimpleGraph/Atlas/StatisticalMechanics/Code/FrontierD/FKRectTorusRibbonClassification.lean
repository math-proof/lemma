import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusRibbonClassification
open Finset StatMech StatMech.FrontierD


/--
[fkRectEulerHomologyDefect_classified_of_ribbonBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRibbonClassification.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_classified_of_ribbonBoundary_eq
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
  (hfullBoundary : S.boundaryComponents Finset.univ = C.dualVertexCount) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 ∨ fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_classified_of_ribbonBoundary R S C hprimal hgenus hboundary hfullBoundary F


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.GenusZeroRibbonEulerDefect
open Finset Equiv StatMech StatMech.FrontierD


/--
[genusZeroRibbonEulerDefect_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusZeroRibbonEulerDefect.lean)
-/
@[path]
private lemma genusZeroRibbonEulerDefect_univ_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
-- given
  (clusters : Finset E -> Nat)
  (hgenus : C.genus = 0)
  (hclusters : clusters Finset.univ = 1)
  (hboundary : R.boundaryComponents Finset.univ = C.dualVertexCount) :
-- imply
  genusOneRibbonEulerDefect R C.primalVertexCount clusters Finset.univ = 0 := by
-- proof
  apply StatMech.FrontierD.genusZeroRibbonEulerDefect_univ R C clusters hgenus hclusters hboundary

/--
[genusZeroRibbonEulerDefect_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusZeroRibbonEulerDefect.lean)
-/
@[path]
private lemma genusZeroRibbonEulerDefect_eq_zero_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {F : Finset E}
-- given
  (clusters : Finset E -> Nat)
  (hgenus : C.genus = 0)
  (hempty : clusters ∅ = C.primalVertexCount)
  (hfullClusters : clusters Finset.univ = 1)
  (hfullBoundary : R.boundaryComponents Finset.univ = C.dualVertexCount)
  (hmonoInsert : ∀ (F : Finset E) (e : E), e ∉ F → genusOneRibbonEulerDefect R C.primalVertexCount clusters F <= genusOneRibbonEulerDefect R C.primalVertexCount clusters (insert e F)) :
-- imply
  genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 0 := by
-- proof
  apply StatMech.FrontierD.genusZeroRibbonEulerDefect_eq_zero R C clusters hgenus hempty hfullClusters hfullBoundary hmonoInsert F


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.GenusOneRibbonEulerDefect
open Finset Equiv StatMech StatMech.FrontierD


/--
[genusOneRibbonEulerDefect_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusOneRibbonEulerDefect.lean)
-/
@[path]
private lemma genusOneRibbonEulerDefect_empty_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {clusters : Finset E → Nat}
-- given
  (hclusters : clusters ∅ = C.primalVertexCount) :
-- imply
  genusOneRibbonEulerDefect R C.primalVertexCount clusters ∅ = 0 := by
-- proof
  apply StatMech.FrontierD.genusOneRibbonEulerDefect_empty R C clusters hclusters

/--
[genusOneRibbonEulerDefect_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusOneRibbonEulerDefect.lean)
-/
@[path]
private lemma genusOneRibbonEulerDefect_univ_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {clusters : Finset E → Nat}
-- given
  (hgenus : C.genus = 1)
  (hclusters : clusters Finset.univ = 1)
  (hboundary : R.boundaryComponents Finset.univ = C.dualVertexCount) :
-- imply
  genusOneRibbonEulerDefect R C.primalVertexCount clusters Finset.univ = 2 := by
-- proof
  apply StatMech.FrontierD.genusOneRibbonEulerDefect_univ R C clusters hgenus hclusters hboundary

/--
[genusOneRibbonEulerDefect_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusOneRibbonEulerDefect.lean)
-/
@[path]
private lemma genusOneRibbonEulerDefect_even_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {clusters : Finset E → Nat}
  {F : Finset E}
-- given
  (hgenus : C.genus = 1) :
-- imply
  Even (genusOneRibbonEulerDefect R C.primalVertexCount clusters F) := by
-- proof
  apply StatMech.FrontierD.genusOneRibbonEulerDefect_even R C clusters hgenus F

/--
[genusOneRibbonEulerDefect_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusOneRibbonEulerDefect.lean)
-/
@[path]
private lemma genusOneRibbonEulerDefect_classified_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {C : CellularRibbonDualData R}
  {clusters : Finset E → Nat}
  {F : Finset E}
-- given
  (hgenus : C.genus = 1)
  (hempty : clusters ∅ = C.primalVertexCount)
  (hfullClusters : clusters Finset.univ = 1)
  (hfullBoundary : R.boundaryComponents Finset.univ = C.dualVertexCount)
  (hmonoInsert : ∀ (F : Finset E) (e : E), e ∉ F → genusOneRibbonEulerDefect R C.primalVertexCount clusters F ≤ genusOneRibbonEulerDefect R C.primalVertexCount clusters (insert e F)) :
-- imply
  genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 0 ∨ genusOneRibbonEulerDefect R C.primalVertexCount clusters F = 2 := by
-- proof
  apply StatMech.FrontierD.genusOneRibbonEulerDefect_classified R C clusters hgenus hempty hfullClusters hfullBoundary hmonoInsert F


-- created on 2026-10-23

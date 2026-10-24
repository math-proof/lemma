import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamDiagonalAdapter
open Finset Classical StatMech StatMech.FrontierA


/--
[grahamLooplessEdges_noDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean)
-/
@[path]
private lemma grahamLooplessEdges_noDiag_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)} :
-- imply
  ∀ e ∈ grahamLooplessEdges E, ¬ e.IsDiag := by
-- proof
  apply StatMech.FrontierA.grahamLooplessEdges_noDiag E

/--
[bond_eq_one_of_isDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean)
-/
@[path]
private lemma bond_eq_one_of_isDiag_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {e : Sym2 V}
-- given
  (he : e.IsDiag) :
-- imply
  bond s e = 1 := by
-- proof
  apply StatMech.FrontierA.bond_eq_one_of_isDiag s e he

/--
[wJ_eq_diagFactor_mul_loopless](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean)
-/
@[path]
private lemma wJ_eq_diagFactor_mul_loopless_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  wJ E J (fun _ => 0) s = Real.exp (∑ e ∈ grahamDiagonalEdges E, J e) * wJ (grahamLooplessEdges E) J (fun _ => 0) s := by
-- proof
  apply StatMech.FrontierA.wJ_eq_diagFactor_mul_loopless E J s

/--
[expJ_eq_looplessEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean)
-/
@[path]
private lemma expJ_eq_looplessEdges_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (J : Sym2 V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  expJ E J (fun _ => 0) f = expJ (grahamLooplessEdges E) J (fun _ => 0) f := by
-- proof
  apply StatMech.FrontierA.expJ_eq_looplessEdges E J f

/--
[grahamLooplessGraph_expectationJ_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean)
-/
@[path]
private lemma grahamLooplessGraph_expectationJ_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  expectationJ (grahamGraph (grahamLooplessEdges E)) 1 J A = expJ E J (fun _ => 0) (spinProd A) := by
-- proof
  apply StatMech.FrontierA.grahamLooplessGraph_expectationJ_eq_expJ E J A


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean)
-/
@[path]
private lemma grahamGraph_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
-- given
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  (grahamGraph E).edgeFinset = E := by
-- proof
  apply StatMech.FrontierA.grahamGraph_edgeFinset E hdiag

/--
[grahamGraph_boltzmannJ_eq_wJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean)
-/
@[path]
private lemma grahamGraph_boltzmannJ_eq_wJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  boltzmannJ (grahamGraph E) 1 J s = wJ E J (fun _ => 0) s := by
-- proof
  apply StatMech.FrontierA.grahamGraph_boltzmannJ_eq_wJ E J hdiag s

/--
[grahamGraph_expectationJ_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean)
-/
@[path]
private lemma grahamGraph_expectationJ_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {A : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  expectationJ (grahamGraph E) 1 J A = expJ E J (fun _ => 0) (spinProd A) := by
-- proof
  apply StatMech.FrontierA.grahamGraph_expectationJ_eq_expJ E J hdiag A

/--
[grahamGraph_expectationJ_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean)
-/
@[path]
private lemma grahamGraph_expectationJ_pair_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hdiag : ∀ e ∈ E, ¬ e.IsDiag) :
-- imply
  expectationJ (grahamGraph E) 1 J (grahamPairSupport x y) = grahamTwoPoint E J x y := by
-- proof
  apply StatMech.FrontierA.grahamGraph_expectationJ_pair E J hdiag x y


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiberClosure
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamLemmaOneMixedCoefficientWeight_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiberClosure.lean)
-/
@[path]
private lemma grahamLemmaOneMixedCoefficientWeight_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e) :
-- imply
  Summable (fun total : G.edgeFinset -> Nat => grahamLemmaOneMixedProfileCoefficient G total j k l m * weight G beta J (ofEdgeFun G total)) := by
-- proof
  apply StatMech.FrontierA.grahamLemmaOneMixedCoefficientWeight_summable G beta J hbeta hJ j k l m

/--
[grahamWeightedLemmaOne_of_fiberMinors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiberClosure.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_fiberMinors_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hminor : forall total : G.edgeFinset -> Nat, GrahamFiberMinor (endsM G total) Finset.univ j k l m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_fiberMinors G beta J hbeta hJ j k l m hminor

/--
[grahamWeightedLemmaOne_of_rowDataRepairHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedLemmaOneFiberClosure.lean)
-/
@[path]
private lemma grahamWeightedLemmaOne_of_rowDataRepairHall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hhall : forall total : G.edgeFinset -> Nat, RowDataRepairHall (endsM G total) Finset.univ j k l m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m <= sourcePairDisconnSum G beta J {j, k} {k, l} k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamWeightedLemmaOne_of_rowDataRepairHall G beta J hbeta hJ j k l m hhall


-- created on 2026-10-23

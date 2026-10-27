import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRemainderAbsorption
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[grahamRemainderAbsorption_of_cutPositiveAssociation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRemainderAbsorption.lean)
-/
@[path]
private lemma grahamRemainderAbsorption_of_cutPositiveAssociation_eq
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
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m)
  (hassoc : GrahamCutPositiveAssociation G beta J m) :
-- imply
  sourcePairDisconnSum G beta J {j, k} ∅ k m * sourcePairDisconnSum G beta J {k, l} ∅ k m + gatedSourcePairSum G beta J {j, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ ¬ CurrentConnected G n k l) * currentSum G beta J ∅ ^ 2 <= sourcePairDisconnSum G beta J {j, l} ∅ k m * currentSum G beta J ∅ ^ 2 := by
-- proof
  apply StatMech.FrontierA.grahamRemainderAbsorption_of_cutPositiveAssociation G beta J hbeta hJ hjk hjl hkl hjm hkm hlm hassoc


-- created on 2026-10-23

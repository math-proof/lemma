import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedEq22Refinement
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[gatedSourcePairSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma gatedSourcePairSum_split_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (J : Sym2 V -> Real)
  (P Q : Current V -> Prop) :
-- imply
  gatedSourcePairSum G beta J A B P = gatedSourcePairSum G beta J A B (fun n => P n ∧ Q n) + gatedSourcePairSum G beta J A B (fun n => P n ∧ ¬ Q n) := by
-- proof
  apply StatMech.FrontierA.gatedSourcePairSum_split G beta J A B P Q

/--
[grahamFirstDisconnection_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamFirstDisconnection_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  sourcePairDisconnSum G beta J {i, j} ∅ i m = gatedSourcePairSum G beta J {i, j} ∅ (fun n => ¬ CurrentConnected G n i m ∧ (CurrentConnected G n i k ∨ CurrentConnected G n i l)) + grahamFirstRemainderMass G beta J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamFirstDisconnection_partition G beta J i j k l m

/--
[grahamSecondDisconnection_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamSecondDisconnection_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  sourcePairDisconnSum G beta J {k, l} ∅ k m = gatedSourcePairSum G beta J {k, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ (CurrentConnected G n k i ∨ CurrentConnected G n k j)) + grahamSecondRemainderMass G beta J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamSecondDisconnection_partition G beta J i j k l m

/--
[grahamMixedDisconnection_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamMixedDisconnection_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  sourcePairDisconnSum G beta J {i, j} {k, l} i k = grahamFirstMixedRemainderMass G beta J i j k l m + grahamSecondMixedRemainderMass G beta J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamMixedDisconnection_partition G beta J i j k l m

/--
[grahamEq22_exact_refinement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamEq22_exact_refinement_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (him : i ≠ m)
  (hjm : j ≠ m) :
-- imply
  let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m let S1 := gatedSourcePairSum G beta J {i, j} ∅ (fun n => ¬ CurrentConnected G n i m ∧ (CurrentConnected G n i k ∨ CurrentConnected G n i l)) let S2 := gatedSourcePairSum G beta J {k, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ (CurrentConnected G n k i ∨ CurrentConnected G n k j)) 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m = -2 * Z * currentSum G beta J {k, l} * S1 - 2 * Cim * S2 - 2 * Z * (currentSum G beta J {k, l} * grahamFirstRemainderMass G beta J i j k l m - Z * grahamFirstMixedRemainderMass G beta J i j k l m) - 2 * ((currentSum G beta J {i, m} * currentSum G beta J {j, m}) * grahamSecondRemainderMass G beta J i j k l m - Z ^ 2 * grahamSecondMixedRemainderMass G beta J i j k l m) := by
-- proof
  apply StatMech.FrontierA.grahamEq22_exact_refinement G beta J hij him hjm

/--
[grahamEq22_survivor_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamEq22_survivor_upper_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m let S1 := gatedSourcePairSum G beta J {i, j} ∅ (fun n => ¬ CurrentConnected G n i m ∧ (CurrentConnected G n i k ∨ CurrentConnected G n i l)) let S2 := gatedSourcePairSum G beta J {k, l} ∅ (fun n => ¬ CurrentConnected G n k m ∧ (CurrentConnected G n k i ∨ CurrentConnected G n k j)) 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m ≤ -2 * Z * currentSum G beta J {k, l} * S1 - 2 * Cim * S2 := by
-- proof
  apply StatMech.FrontierA.grahamEq22_survivor_upper_bound G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm

/--
[grahamEq22_mixed_disconnection_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedEq22Refinement.lean)
-/
@[path]
private lemma grahamEq22_mixed_disconnection_upper_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 ≤ beta)
  (hJ : ∀ e, 0 ≤ J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  let Z := currentSum G beta J ∅ let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * Cim * sourcePairDisconnSum G beta J {k, l} ∅ k m ≤ -2 * Z * currentSum G beta J {k, l} * sourcePairDisconnSum G beta J {i, k} {k, j} i m - 2 * Cim * sourcePairDisconnSum G beta J {k, i} {i, l} k m := by
-- proof
  apply StatMech.FrontierA.grahamEq22_mixed_disconnection_upper_bound G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm


-- created on 2026-10-23

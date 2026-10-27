import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedAuxiliaryAlgebra
open Finset SimpleGraph Classical StatMech StatMech.FrontierA


/--
[gc37_sourcePairConnSum_eq_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma gc37_sourcePairConnSum_eq_gated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  StatMech.Walls.gc37_sourcePairConnSum G beta J A B u v = gatedSourcePairSum G beta J A B (fun n => CurrentConnected G n u v) := by
-- proof
  apply StatMech.FrontierA.gc37_sourcePairConnSum_eq_gated G beta J A B u v

/--
[graham_two_connections_iff_allThree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma graham_two_connections_iff_allThree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k l : V}
-- given
  (p q : ↥G.edgeFinset -> Nat)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (hp : sources G (ofEdgeFun G p) = {i, j, k, l})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  (CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) i k ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) k l) ↔ grahamAllThreeConnected G (ofEdgeFun G (fun e => p e + q e)) i j k l := by
-- proof
  apply StatMech.FrontierA.graham_two_connections_iff_allThree G p q hij hik hil hjk hjl hkl hp hq

/--
[grahamAllThreeMass_eq_pairConnectionMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma grahamAllThreeMass_eq_pairConnectionMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l) :
-- imply
  gatedSourcePairSum G beta J {i, j, k, l} ∅ (fun n => grahamAllThreeConnected G n i j k l) = StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} {k, l} i k := by
-- proof
  apply StatMech.FrontierA.grahamAllThreeMass_eq_pairConnectionMass G beta J hij hik hil hjk hjl hkl

/--
[grahamAuxConnectionMass_eq_currentSums](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma grahamAuxConnectionMass_eq_currentSums_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (him : i ≠ m)
  (hjm : j ≠ m) :
-- imply
  StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m = currentSum G beta J {i, m} * currentSum G beta J {j, m} := by
-- proof
  apply StatMech.FrontierA.grahamAuxConnectionMass_eq_currentSums G beta J hij him hjm

/--
[grahamAuxiliary_disconnection_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma grahamAuxiliary_disconnection_decomposition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real) :
-- imply
  let Z := currentSum G beta J ∅ let Cik := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} {k, l} i k let Cim := StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m let Ckm := StatMech.Walls.gc37_sourcePairConnSum G beta J {k, l} ∅ k m let Dik := sourcePairDisconnSum G beta J {i, j} {k, l} i k let Dim := sourcePairDisconnSum G beta J {i, j} ∅ i m let Dkm := sourcePairDisconnSum G beta J {k, l} ∅ k m (-2 * Z ^ 2 * Cik + 2 * Cim * Ckm = 2 * Z ^ 2 * Dik - 2 * Dim * currentSum G beta J {k, l} * Z - 2 * Cim * Dkm) := by
-- proof
  apply StatMech.FrontierA.grahamAuxiliary_disconnection_decomposition G beta J i j k l m

/--
[grahamCurrentSum_preEq22](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedAuxiliaryAlgebra.lean)
-/
@[path]
private lemma grahamCurrentSum_preEq22_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hkl : k ≠ l)
  (him : i ≠ m)
  (hjm : j ≠ m)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  let Z := currentSum G beta J ∅ Z ^ 2 * (currentSum G beta J {i, j, k, l} * Z - currentSum G beta J {i, j} * currentSum G beta J {k, l} - currentSum G beta J {i, k} * currentSum G beta J {j, l} - currentSum G beta J {i, l} * currentSum G beta J {j, k}) + 2 * (currentSum G beta J {i, m} * currentSum G beta J {j, m}) * (currentSum G beta J {k, m} * currentSum G beta J {l, m}) = 2 * Z ^ 2 * sourcePairDisconnSum G beta J {i, j} {k, l} i k - 2 * sourcePairDisconnSum G beta J {i, j} ∅ i m * currentSum G beta J {k, l} * Z - 2 * StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m * sourcePairDisconnSum G beta J {k, l} ∅ k m := by
-- proof
  apply StatMech.FrontierA.grahamCurrentSum_preEq22 G beta J hij hik hil hjk hjl hkl him hjm hkm hlm


-- created on 2026-10-23

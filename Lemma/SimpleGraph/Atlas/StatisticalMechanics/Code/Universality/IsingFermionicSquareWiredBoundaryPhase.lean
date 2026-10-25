import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredBoundaryPhase
open StatMech StatMech.Universality


/--
[fkIsingSquareSignedEighthTurn_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareSignedEighthTurn_modEq_eq
  {a b : Int} :
-- imply
  fkIsingSquareSignedEighthTurn a b ≡ b - a [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareSignedEighthTurn_modEq a b

/--
[fkIsingSquareWiredDirectedTangentCode_incidenceMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_incidenceMate_eq
  {n : Nat}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (fkIsingSquareWiredIncidenceMate n x) = fkIsingSquareWiredDirectedTangentCode n hn x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_incidenceMate n hn x

/--
[fkIsingSquareWiredBondTurn_modEq_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondTurn_modEq_directedTangent_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondTurn n hn d (fkIsingSquareWiredBondMate n hn d) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareWiredBondMate n hn d)) - fkIsingSquareWiredDirectedTangentCode n hn (.bond d) [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondTurn_modEq_directedTangent n hn d

/--
[fkIsingSquareWiredDirectedTangentCode_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_source_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn .source = 9 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_source n hn

/--
[fkIsingSquareWiredDirectedTangentCode_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredDirectedTangentCode_terminal_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn .terminal = 3 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDirectedTangentCode_terminal n hn

/--
[fkIsingSquareWiredTransitionTurn_modEq_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_modEq_directedTangent_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareWiredTransitionTurn n hn omega x y ≡ fkIsingSquareWiredDirectedTangentCode n hn y - fkIsingSquareWiredDirectedTangentCode n hn x [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_modEq_directedTangent n hn omega hxy

/--
[fkIsingSquareWiredRawTurnCount_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_source_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega .source = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_source n hn omega

/--
[fkIsingSquareWiredExplorationOrder_adj_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationOrder_adj_succ_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i + 1 < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).Adj (fkIsingSquareWiredExplorationOrder n hn omega)[i] (fkIsingSquareWiredExplorationOrder n hn omega)[i + 1] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationOrder_adj_succ n hn omega i hi

/--
[fkIsingSquareWiredRawTurnCount_getElem_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_getElem_modEq_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i < (fkIsingSquareWiredExplorationOrder n hn omega).length) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega (fkIsingSquareWiredExplorationOrder n hn omega)[i] ≡ fkIsingSquareWiredDirectedTangentCode n hn (fkIsingSquareWiredExplorationOrder n hn omega)[i] - fkIsingSquareWiredDirectedTangentCode n hn .source [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_getElem_modEq n hn omega i hi

/--
[fkIsingSquareWiredRawTurnCount_modEq_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_modEq_directedTangent_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega z ≡ fkIsingSquareWiredDirectedTangentCode n hn z - fkIsingSquareWiredDirectedTangentCode n hn .source [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_modEq_directedTangent n hn omega z hz

/--
[fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredBoundaryPhase.lean)
-/
@[path]
private lemma fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredPhysicalTurnCount n hn omega z ≡ fkIsingSquareWiredDirectedTangentCode n hn z - fkIsingSquareWiredDirectedTangentCode n hn .terminal [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPhysicalTurnCount_modEq_directedTangent n hn omega z hz


-- created on 2026-10-23

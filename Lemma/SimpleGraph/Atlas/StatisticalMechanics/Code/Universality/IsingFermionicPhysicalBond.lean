import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBond.Part2
open StatMech StatMech.Universality


/--
[fkIsingSquareOrientedPrincipalBondTurn_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareOrientedPrincipalBondTurn_reverse_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareOrientedPrincipalBondTurn n hn (fkIsingSquareWiredBondMate n hn d) d = -fkIsingSquareOrientedPrincipalBondTurn n hn d (fkIsingSquareWiredBondMate n hn d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareOrientedPrincipalBondTurn_reverse n hn d

/--
[fkIsingSquareWiredBondTurn_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondTurn_reverse_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBondTurn n hn (fkIsingSquareWiredBondMate n hn d) d = -fkIsingSquareWiredBondTurn n hn d (fkIsingSquareWiredBondMate n hn d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondTurn_reverse n hn d

/--
[fkIsingSquareWired_bondMate_infix_explorationOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWired_bondMate_infix_explorationOrder_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (h : (.bond d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  [(.bond d : FKIsingSquareWiredCarrier n), .bond (fkIsingSquareWiredBondMate n hn d)] <:+: fkIsingSquareWiredExplorationOrder n hn omega ∨ [(.bond (fkIsingSquareWiredBondMate n hn d) : FKIsingSquareWiredCarrier n), .bond d] <:+: fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_bondMate_infix_explorationOrder n hn omega d hsource hterminal h

/--
[fkIsingSquareWiredRawTurnCount_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredRawTurnCount_bondMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (h : (.bond d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredRawTurnCount n hn omega (.bond (fkIsingSquareWiredBondMate n hn d)) = fkIsingSquareWiredRawTurnCount n hn omega (.bond d) + fkIsingSquareWiredBondTurn n hn d (fkIsingSquareWiredBondMate n hn d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRawTurnCount_bondMate n hn omega d hsource hterminal h

/--
[fkIsingSquareWiredLiftedWinding_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredLiftedWinding_bondMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
  (h : (.bond d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn omega (.bond (fkIsingSquareWiredBondMate n hn d)) = fkIsingSquareWiredLiftedWinding n hn omega (.bond d) + (fkIsingSquareWiredBondTurn n hn d (fkIsingSquareWiredBondMate n hn d) : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLiftedWinding_bondMate n hn omega d hsource hterminal h

/--
[fkIsingSquareWired_bondMate_mem_trace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWired_bondMate_mem_trace_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (.bond (fkIsingSquareWiredBondMate n hn d) : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega ↔ (.bond d : FKIsingSquareWiredCarrier n) ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_bondMate_mem_trace_iff n hn omega d hsource hterminal

/--
[fkIsingSquareWiredBondPhase_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondPhase_normSq_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  Complex.normSq (fkIsingSquareWiredBondPhase n hn d) = 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondPhase_normSq n hn d

/--
[fkIsingSquareWired_fermionicSummand_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicSummand_bondMate_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.bond (fkIsingSquareWiredBondMate n hn d)) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicSummand_bondMate n hn omega d hsource hterminal

/--
[fkIsingSquareWired_fermionicObservable_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicObservable_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond (fkIsingSquareWiredBondMate n hn d)) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.bond d) * fkIsingSquareWiredBondPhase n hn d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicObservable_bondMate n hn d hsource hterminal

/--
[fkIsingSquareWiredPrimitiveIncrement_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_bondMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.bond (fkIsingSquareWiredBondMate n hn d)) = fkIsingSquareWiredPrimitiveIncrement n hn (.bond d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_bondMate n hn d hsource hterminal

/--
[fkIsingSquareWiredPrimitiveIncrement_bondDartMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_bondDartMate_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
  (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquareWiredBondMate n hn d)) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart d) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_bondDartMate n hn d hsource hterminal

/--
[fkIsingSquareWiredPrimitiveIncrement_bond_local_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalBond.lean)
-/
@[path]
private lemma fkIsingSquareWiredPrimitiveIncrement_bond_local_closed_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .west)) + fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .east)) = fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .south)) + fkIsingSquareWiredPrimitiveIncrement n hn (.bond (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredPrimitiveIncrement_bond_local_closed n hn e


-- created on 2026-10-23

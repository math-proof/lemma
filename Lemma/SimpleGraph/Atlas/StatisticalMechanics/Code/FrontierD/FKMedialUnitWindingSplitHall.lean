import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialBlackBoundaryCycleWeight_split_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialUnitWindingSplitHall.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryCycleWeight_split_of_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  [AddCommGroup A]
-- given
  (hreach : (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v))
  (oldWeight newWeight : FKMedialBlackDart T -> A)
  (haway : forall d, d ≠ fkMedialBlackDart0 v -> d ≠ fkMedialBlackDart1 v -> oldWeight d = newWeight d)
  (hpair : oldWeight (fkMedialBlackDart0 v) + oldWeight (fkMedialBlackDart1 v) = newWeight (fkMedialBlackDart0 v) + newWeight (fkMedialBlackDart1 v)) :
-- imply
  permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing) (fkMedialBlackDart0 v) oldWeight = permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart0 v) newWeight + permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart1 v) newWeight := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryCycleWeight_split_of_reachable pairing v hreach oldWeight newWeight haway hpair

/--
[fkMedialBlackBoundaryCycleWeight_split_two_units](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialUnitWindingSplitHall.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryCycleWeight_split_two_units_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
-- given
  (hreach : (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v))
  (oldWeight newWeight : FKMedialBlackDart T -> Int)
  (haway : forall d, d ≠ fkMedialBlackDart0 v -> d ≠ fkMedialBlackDart1 v -> oldWeight d = newWeight d)
  (hpair : oldWeight (fkMedialBlackDart0 v) + oldWeight (fkMedialBlackDart1 v) = newWeight (fkMedialBlackDart0 v) + newWeight (fkMedialBlackDart1 v))
  (hold : permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing) (fkMedialBlackDart0 v) oldWeight = 2)
  (hfirst : 0 < permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart0 v) newWeight)
  (hsecond : 0 < permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart1 v) newWeight) :
-- imply
  permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart0 v) newWeight = 1 /\ permCycleClassWeightSum (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v)) (fkMedialBlackDart1 v) newWeight = 1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryCycleWeight_split_two_units pairing v hreach oldWeight newWeight haway hpair hold hfirst hsecond

/--
[booleanTwoUnitComponentDownRelation_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialUnitWindingSplitHall.lean)
-/
@[path]
private lemma booleanTwoUnitComponentDownRelation_hall_eq
  {T : EvenTorus} :
-- imply
  forall sources : Finset (BooleanLayer Bool 2), sources.card <= (Finset.univ.filter fun target : BooleanLayer Bool 1 => ∃ source ∈ sources, booleanMiddleLayerDownRelation source target).card := by
-- proof
  apply StatMech.FrontierD.booleanTwoUnitComponentDownRelation_hall


-- created on 2026-10-23

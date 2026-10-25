import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
open StatMech StatMech.Universality StatMech.Universality.HexAWBrickCycle


/--
[hexBrickPos_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hexBrickPos_neighbor_eq
  {c : HexAWCoord}
  {e : Fin 3} :
-- imply
  hexBrickPos (hexAWNeighbor c e) = hexBrickPos c + stepOf (hexBrickDir (hexAWHeadingMod c e)) := by
-- proof
  apply StatMech.Universality.hexBrickPos_neighbor c e

/--
[hexBrickPos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hexBrickPos_injective_eq :
-- imply
  Function.Injective hexBrickPos := by
-- proof
  apply StatMech.Universality.hexBrickPos_injective

/--
[step_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma step_eq_sub_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n}
  {i : Fin n} :
-- imply
  stepOf (C.direction i) = hexBrickPos (C.coord (i + 1)) - hexBrickPos (C.coord i) := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.step_eq_sub C i

/--
[closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma closed_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n} :
-- imply
  ∑ i, stepOf (C.direction i) = 0 := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.closed C

/--
[pos_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma pos_eq_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n}
  {k : Fin n} :
-- imply
  pos C.direction k = hexBrickPos (C.coord k) - hexBrickPos (C.coord 0) := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.pos_eq C k

/--
[pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma pos_injective_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n} :
-- imply
  Function.Injective (pos C.direction) := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.pos_injective C

/--
[hexBrickDir_turn_ne_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hexBrickDir_turn_ne_opposite_eq
  {t : ℤ}
-- given
  (h : Fin 6)
  (ht : t = 1 ∨ t = -1) :
-- imply
  hexBrickDir (hexHeadingTurn h t) ≠ hexBrickDir h + 2 := by
-- proof
  apply StatMech.Universality.hexBrickDir_turn_ne_opposite h t ht

/--
[hexBrick_local_turn_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hexBrick_local_turn_identity_eq
  {t : ℤ}
-- given
  (h : Fin 6)
  (ht : t = 1 ∨ t = -1) :
-- imply
  2 * t + 3 * ons_turnPow (hexBrickDir h) (hexBrickDir (hexHeadingTurn h t)) = hexBrickTurnPotential (hexHeadingTurn h t) - hexBrickTurnPotential h := by
-- proof
  apply StatMech.Universality.hexBrick_local_turn_identity h t ht

/--
[hexBrick_turn_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hexBrick_turn_telescope_eq
  {n : ℕ}
  [NeZero n]
  {turn : Fin n → ℤ}
-- given
  (heading : Fin n → Fin 6)
  (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
  (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i)) :
-- imply
  2 * (∑ i, turn i) + 3 * (∑ i, ons_turnPow (hexBrickDir (heading i)) (hexBrickDir (heading (i + 1)))) = 0 := by
-- proof
  apply StatMech.Universality.hexBrick_turn_telescope heading turn hlegal hstep

/--
[hex_turnSum_eq_neg_six_of_interiorOnLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hex_turnSum_eq_neg_six_of_interiorOnLeft_eq
  {n : ℕ}
  [NeZero n]
  {turn : Fin n → ℤ}
-- given
  (heading : Fin n → Fin 6)
  (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
  (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
  (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
  (hsimple : Function.Injective (pos (fun i => hexBrickDir (heading i))))
  (hn : 3 ≤ n)
  (horient : HexBrickInteriorOnLeft heading) :
-- imply
  (∑ i, turn i) = -6 := by
-- proof
  apply StatMech.Universality.hex_turnSum_eq_neg_six_of_interiorOnLeft heading turn hlegal hstep hclosed hsimple hn horient

/--
[hex_turnSum_eq_six_or_neg_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma hex_turnSum_eq_six_or_neg_six_eq
  {n : ℕ}
  [NeZero n]
  {turn : Fin n → ℤ}
-- given
  (heading : Fin n → Fin 6)
  (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
  (hstep : ∀ i, heading (i + 1) = hexHeadingTurn (heading i) (turn i))
  (hclosed : ∑ i, stepOf (hexBrickDir (heading i)) = 0)
  (hsimple : Function.Injective (pos (fun i => hexBrickDir (heading i))))
  (hn : 3 ≤ n) :
-- imply
  (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
-- proof
  apply StatMech.Universality.hex_turnSum_eq_six_or_neg_six heading turn hlegal hstep hclosed hsimple hn

/--
[HexAWBrickCycle.turnSum_eq_six_or_neg_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma turnSum_eq_six_or_neg_six_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n}
  {turn : Fin n → ℤ}
-- given
  (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
  (hstep : ∀ i, C.heading (i + 1) = hexHeadingTurn (C.heading i) (turn i))
  (hn : 3 ≤ n) :
-- imply
  (∑ i, turn i) = 6 ∨ (∑ i, turn i) = -6 := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.turnSum_eq_six_or_neg_six C turn hlegal hstep hn

/--
[HexAWBrickCycle.turnSum_eq_neg_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean)
-/
@[path]
private lemma turnSum_eq_neg_six_eq
  {n : ℕ}
  [NeZero n]
  {C : HexAWBrickCycle n}
  {turn : Fin n → ℤ}
-- given
  (hlegal : ∀ i, turn i = 1 ∨ turn i = -1)
  (hstep : ∀ i, C.heading (i + 1) = hexHeadingTurn (C.heading i) (turn i))
  (hn : 3 ≤ n)
  (horient : HexBrickInteriorOnLeft C.heading) :
-- imply
  (∑ i, turn i) = -6 := by
-- proof
  apply StatMech.Universality.HexAWBrickCycle.turnSum_eq_neg_six C turn hlegal hstep hn horient


-- created on 2026-10-23

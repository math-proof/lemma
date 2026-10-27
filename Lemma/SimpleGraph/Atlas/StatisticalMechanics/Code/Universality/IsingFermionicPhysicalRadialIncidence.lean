import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
open StatMech StatMech.Universality


/--
[fkIsingSquareInteriorRadialBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialBondMate_involutive_eq
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Function.Involutive (fkIsingSquareInteriorRadialBondMate n hn) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialBondMate_involutive n hn

/--
[fkIsingSquareInteriorRadialBondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialBondMate_ne_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialBondMate n hn d ≠ d := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialBondMate_ne n hn d

/--
[fkIsingSquareInteriorRadialDart_ne_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialDart_ne_source_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  d.1 ≠ fkIsingSquareWiredSourceDart n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialDart_ne_source n hn d

/--
[fkIsingSquareInteriorRadialDart_ne_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialDart_ne_terminal_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  d.1 ≠ fkIsingSquareWiredTerminalDart n hn := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialDart_ne_terminal n hn d

/--
[fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n)
  (hcode : fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
-- imply
  fkIsingSquareWiredBondTurn n hn d.1 (fkIsingSquareInteriorRadialBondMate n hn d).1 = 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_bondTurn_eq_zero_of_directedTangentCode_eq n hn d hcode

/--
[fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n)
  (hcode : fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareInteriorRadialBondMate n hn d)) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond d.1) [ZMOD 8]) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart d.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_fermionicObservable_bondMate_eq_of_code_modEq n hn d hcode

/--
[fkIsingSquareInteriorRadial_endpoint_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_endpoint_bondMate_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareInteriorRadialBondMate n hn d).1 = fkIsingSquareDartEndpoint n d.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_endpoint_bondMate n hn d

/--
[fkIsingSquareInteriorRadial_faceKey_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_faceKey_bondMate_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWedgeFaceKey n (fkIsingSquareInteriorRadialBondMate n hn d).1 = fkIsingSquareWedgeFaceKey n d.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_faceKey_bondMate n hn d

/--
[fkIsingSquareInteriorRadial_increment_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_increment_bondMate_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredPrimitiveIncrement n hn (.dart (fkIsingSquareInteriorRadialBondMate n hn d).1) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_increment_bondMate n hn d

/--
[fkIsingSquareInteriorRadialEndpoint_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialEndpoint_mk_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialEndpoint n hn (Quot.mk _ d) = fkIsingSquareDartEndpoint n d.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialEndpoint_mk n hn d

/--
[fkIsingSquareInteriorRadialFaceKey_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialFaceKey_mk_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialFaceKey n hn (Quot.mk _ d) = fkIsingSquareWedgeFaceKey n d.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialFaceKey_mk n hn d

/--
[fkIsingSquareInteriorRadialIncrement_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialIncrement_mk_eq
  {n : Nat}
  {d : FKIsingSquareInteriorRadialDart n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn (Quot.mk _ d) = fkIsingSquareWiredPrimitiveIncrement n hn (.dart d.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialIncrement_mk n hn d

/--
[fkIsingSquareInteriorRadialIncrement_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialIncrement_nonneg_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  0 ≤ fkIsingSquareInteriorRadialIncrement n hn e := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialIncrement_nonneg n hn e

/--
[fkIsingSquareInteriorRadialFaceKey_isInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialFaceKey_isInterior_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorFaceKey n (fkIsingSquareInteriorRadialFaceKey n hn e) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialFaceKey_isInterior n hn e

/--
[fkIsingSquareInteriorRadial_coordinates_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadial_coordinates_adjacent_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialIncidence n hn}
-- given
  (hn : 0 < n) :
-- imply
  let u := fkIsingSquareInteriorRadialPrimalCoordinate n hn e let p := fkIsingSquareInteriorRadialFaceCoordinate n hn e p = (u.1 + 1, u.2) ∨ p = (u.1, u.2 + 1) ∨ p = (u.1 - 1, u.2) ∨ p = (u.1, u.2 - 1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadial_coordinates_adjacent n hn e

/--
[fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialCell n}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e s) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (e.1, s))) (fkIsingSquareWiredFullMedialObservable n hn e.1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialCell_increment_eq_normSq_full_projection n hn e s

/--
[fkIsingSquareInteriorRadialCell_increment_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialIncidence.lean)
-/
@[path]
private lemma fkIsingSquareInteriorRadialCell_increment_closed_eq
  {n : Nat}
  {e : FKIsingSquareInteriorRadialCell n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .west) + fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .east) = fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .south) + fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareInteriorRadialCellIncidence n hn e .north) := by
-- proof
  apply StatMech.Universality.fkIsingSquareInteriorRadialCell_increment_closed n hn e


-- created on 2026-10-23

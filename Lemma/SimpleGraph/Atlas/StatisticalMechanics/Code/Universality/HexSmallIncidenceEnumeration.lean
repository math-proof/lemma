import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part5
open StatMech StatMech.Universality StatMech.Universality.HexFiniteStripCoreIncidenceEnumeration


/--
[hexVBC_contourFamily_singleton_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexVBC_contourFamily_singleton_q_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexContourFamily (hexVBCRegion a h0).inRegion a h0 ({hexConcreteQ a h0} : Set ℂ) = {[-1]} := by
-- proof
  apply StatMech.Universality.hexVBC_contourFamily_singleton_q a h0

/--
[hexVBC_contourFamily_singleton_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexVBC_contourFamily_singleton_r_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexContourFamily (hexVBCRegion a h0).inRegion a h0 ({hexConcreteR a h0} : Set ℂ) = {[1]} := by
-- proof
  apply StatMech.Universality.hexVBC_contourFamily_singleton_r a h0

/--
[hexVBC_contourSum_singleton_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexVBC_contourSum_singleton_q_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexContourSum (hexVBCRegion a h0).inRegion a h0 ({hexConcreteQ a h0} : Set ℂ) x = x ^ 2 := by
-- proof
  apply StatMech.Universality.hexVBC_contourSum_singleton_q a h0 x

/--
[hexVBC_contourSum_singleton_r](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexVBC_contourSum_singleton_r_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexContourSum (hexVBCRegion a h0).inRegion a h0 ({hexConcreteR a h0} : Set ℂ) x = x ^ 2 := by
-- proof
  apply StatMech.Universality.hexVBC_contourSum_singleton_r a h0 x

/--
[hexSmallCellIncidence_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCellIncidence_mem_eq
  {a : ℂ}
  {j : Fin 3}
-- given
  (h0 : ℤ) :
-- imply
  hexSmallCellIncidence j ∈ (hexUncondDomain a h0).incidences := by
-- proof
  apply StatMech.Universality.hexSmallCellIncidence_mem a h0 j

/--
[hexSmallCellIncidence_boundary_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCellIncidence_boundary_mem_eq
  {a : ℂ}
  {j : Fin 3}
-- given
  (h0 : ℤ) :
-- imply
  hexSmallCellIncidence j ∈ (hexUncondDomain a h0).incidences \ (hexUncondPairing a h0).interior := by
-- proof
  apply StatMech.Universality.hexSmallCellIncidence_boundary_mem a h0 j

/--
[hexSmallCellIncidence_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCellIncidence_eq_eq
  {a : ℂ}
  {e : HexIncidence (Fin 1)}
-- given
  (h0 : ℤ)
  (he : e ∈ (hexUncondDomain a h0).incidences) :
-- imply
  e = hexSmallCellIncidence e.edge := by
-- proof
  apply StatMech.Universality.hexSmallCellIncidence_eq a h0 e he

/--
[hexUncondMid_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexUncondMid_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hexUncondMid a h0) := by
-- proof
  apply StatMech.Universality.hexUncondMid_injective a h0

/--
[exists_startIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma exists_startIncidence_eq
  [DecidableEq V]
  {R : HexFiniteRegion}
  {h0 : ℤ}
  {D : HexDomain V}
  {P : D.InteriorPairing}
  {C : HexFiniteStripBoundaryCore R h0 D P}
  {E : HexFiniteStripCoreIncidenceEnumeration C} :
-- imply
  ∃ eA : HexIncidence V, hexFiniteStripPhysicalStartFiber (R := R) P = {eA} := by
-- proof
  apply StatMech.Universality.HexFiniteStripCoreIncidenceEnumeration.exists_startIncidence E

/--
[hexSmallCell_hgeom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCell_hgeom_eq
  {a : ℂ}
  {v : Fin 1}
  {j : Fin 3}
-- given
  (h0 : ℤ) :
-- imply
  (hexUncondDomain a h0).mid v j - (hexUncondDomain a h0).pos v = (1 / 2 : ℂ) * hexUnit (hexSmallCellHeading h0 j) := by
-- proof
  apply StatMech.Universality.hexSmallCell_hgeom a h0 v j

/--
[hexSmallCell_boundary_identity_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCell_boundary_identity_false_eq :
-- imply
  hexBdryCt * (hexChi ^ 2) + hexChi ^ 2 ≠ hexChi := by
-- proof
  apply StatMech.Universality.hexSmallCell_boundary_identity_false

/--
[hexSmallCell_noFourPhaseData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCell_noFourPhaseData_eq
  {a : ℂ}
  {G : HexRegion}
-- given
  (h0 : ℤ) :
-- imply
  ¬ Nonempty (HexFiniteStripFourPhaseData (hexSmallCellBoundaryCore a h0) G) := by
-- proof
  apply StatMech.Universality.hexSmallCell_noFourPhaseData a h0 G

/--
[hexSmallCell_noFourPhaseLiftData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCell_noFourPhaseLiftData_eq
  {a : ℂ}
  {G : HexRegion} :
-- imply
  ¬ Nonempty (HexFiniteStripFourPhaseLiftData (hexSmallCellCoreOrientation a) G) := by
-- proof
  apply StatMech.Universality.hexSmallCell_noFourPhaseLiftData a G

/--
[hexSmallCell_noLegacyBoundaryData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean)
-/
@[path]
private lemma hexSmallCell_noLegacyBoundaryData_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ¬ ∃ B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0 (hexUncondDomain a h0) (hexUncondPairing a h0), B.sides = hexSmallCellSides a h0 := by
-- proof
  apply StatMech.Universality.hexSmallCell_noLegacyBoundaryData a h0


-- created on 2026-10-23

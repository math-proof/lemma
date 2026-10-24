import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[card_fkMedialVerticallyWindingComponents_le_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma card_fkMedialVerticallyWindingComponents_le_total_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  (fkMedialVerticallyWindingComponents pairing).card ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
-- proof
  apply StatMech.FrontierD.card_fkMedialVerticallyWindingComponents_le_total pairing

/--
[fkMedialDartIncoming_checkerArrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkMedialDartIncoming_checkerArrows_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {d : FKMedialDart T} :
-- imply
  fkMedialDartIncoming (fkMedialCheckerArrows T) d = fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialDartIncoming_checkerArrows T d

/--
[fkMedialCheckerArrows_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkMedialCheckerArrows_compatible_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  ∀ v, fkLoopPairingCompatible (pairing v) (fkMedialCheckerArrows T) v := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerArrows_compatible T pairing

/--
[fkMedialDartIncoming_eq_checkerColor_iff_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkMedialDartIncoming_eq_checkerColor_iff_of_adj_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {d e : FKMedialDart T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
  (hde : (fkMedialLoopGraph T pairing).Adj d e) :
-- imply
  (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔ fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
-- proof
  apply StatMech.FrontierD.fkMedialDartIncoming_eq_checkerColor_iff_of_adj pairing arrows hcompat hde

/--
[fkMedialDartIncoming_eq_checkerColor_iff_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkMedialDartIncoming_eq_checkerColor_iff_of_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {d e : FKMedialDart T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
  (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
-- imply
  (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔ fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
-- proof
  apply StatMech.FrontierD.fkMedialDartIncoming_eq_checkerColor_iff_of_reachable pairing arrows hcompat hde

/--
[fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {arrows : SixVertexArrows T}
  {i : Fin T.width}
-- given
  (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) = fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
-- imply
  fkOrientedVerticalSeamSign T arrows i = fkMedialCanonicalVerticalSeamSign T i := by
-- proof
  apply StatMech.FrontierD.fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq T arrows i h

/--
[fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {arrows : SixVertexArrows T}
  {i : Fin T.width}
-- given
  (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) ≠ fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
-- imply
  fkOrientedVerticalSeamSign T arrows i = -fkMedialCanonicalVerticalSeamSign T i := by
-- proof
  apply StatMech.FrontierD.fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne T arrows i h

/--
[fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {C : FKMedialLoop T pairing}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v) :
-- imply
  fkOrientedMedialLoopVerticalFlux pairing arrows C = fkMedialLoopCanonicalVerticalFlux pairing C ∨ fkOrientedMedialLoopVerticalFlux pairing arrows C = -fkMedialLoopCanonicalVerticalFlux pairing C := by
-- proof
  apply StatMech.FrontierD.fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg pairing arrows hcompat C

/--
[fkOrientedMedialLoopVerticalFlux_natAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedMedialLoopVerticalFlux_natAbs_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {C : FKMedialLoop T pairing}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v) :
-- imply
  (fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs = (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
-- proof
  apply StatMech.FrontierD.fkOrientedMedialLoopVerticalFlux_natAbs pairing arrows hcompat C

/--
[fkOrientedMedialLoopVerticalFlux_arrowsOfMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedMedialLoopVerticalFlux_arrowsOfMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {mode : FKMedialLoop T pairing → Bool}
  {C : FKMedialLoop T pairing} :
-- imply
  fkOrientedMedialLoopVerticalFlux pairing (FKMedialTurningFiber.arrowsOfMode pairing mode) C = if mode C then -fkMedialLoopCanonicalVerticalFlux pairing C else fkMedialLoopCanonicalVerticalFlux pairing C := by
-- proof
  apply StatMech.FrontierD.fkOrientedMedialLoopVerticalFlux_arrowsOfMode pairing mode C

/--
[fkOrientedMedialLoopVerticalFlux_downwardMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedMedialLoopVerticalFlux_downwardMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {C : FKMedialLoop T pairing} :
-- imply
  fkOrientedMedialLoopVerticalFlux pairing (FKMedialTurningFiber.arrowsOfMode pairing (fkMedialDownwardVerticalMode pairing)) C = -((fkMedialLoopCanonicalVerticalFlux pairing C).natAbs : Int) := by
-- proof
  apply StatMech.FrontierD.fkOrientedMedialLoopVerticalFlux_downwardMode pairing C

/--
[sum_fkOrientedMedialLoopVerticalFlux_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma sum_fkOrientedMedialLoopVerticalFlux_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T} :
-- imply
  (∑ C : FKMedialLoop T pairing, fkOrientedMedialLoopVerticalFlux pairing arrows C) = fkOrientedLoopVerticalFlux T arrows := by
-- proof
  apply StatMech.FrontierD.sum_fkOrientedMedialLoopVerticalFlux_eq pairing arrows

/--
[fkOrientedLoopVerticalFlux_downwardMode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedLoopVerticalFlux_downwardMode_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  fkOrientedLoopVerticalFlux T (FKMedialTurningFiber.arrowsOfMode pairing (fkMedialDownwardVerticalMode pairing)) = -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopVerticalFlux_downwardMode pairing

/--
[fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (mode : FKMedialLoop T pairing -> Bool)
  (hmode : forall C, C ∈ fkMedialVerticallyWindingComponents pairing -> mode C = fkMedialDownwardVerticalMode pairing C) :
-- imply
  fkOrientedLoopVerticalFlux T (FKMedialTurningFiber.arrowsOfMode pairing mode) = -(fkMedialUnorientedVerticalWindingTotal pairing : Int) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopVerticalFlux_eq_downwardMode_of_eq_on_windingComponents pairing mode hmode

/--
[even_fkMedialUnorientedVerticalWindingTotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma even_fkMedialUnorientedVerticalWindingTotal_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  Even (fkMedialUnorientedVerticalWindingTotal pairing) := by
-- proof
  apply StatMech.FrontierD.even_fkMedialUnorientedVerticalWindingTotal pairing

/--
[two_mul_half_fkMedialUnorientedVerticalWindingTotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma two_mul_half_fkMedialUnorientedVerticalWindingTotal_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  2 * (fkMedialUnorientedVerticalWindingTotal pairing / 2) = fkMedialUnorientedVerticalWindingTotal pairing := by
-- proof
  apply StatMech.FrontierD.two_mul_half_fkMedialUnorientedVerticalWindingTotal pairing

/--
[card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (hU : fkMedialUnorientedVerticalWindingTotal pairing / 2 = 1) :
-- imply
  (fkMedialVerticallyWindingComponents pairing).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.card_fkMedialVerticallyWindingComponents_le_two_of_half_eq_one pairing hU

/--
[natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v) :
-- imply
  (fkOrientedLoopVerticalFlux T arrows).natAbs ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
-- proof
  apply StatMech.FrontierD.natAbs_fkOrientedLoopVerticalFlux_le_unorientedWindingTotal pairing arrows hcompat

/--
[two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {r : Nat}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
  (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
-- imply
  2 * r ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
-- proof
  apply StatMech.FrontierD.two_mul_le_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul pairing arrows hcompat r hflux

/--
[le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T}
  {r : Nat}
-- given
  (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
  (hflux : fkOrientedLoopVerticalFlux T arrows = -(2 * (r : Int))) :
-- imply
  r ≤ fkMedialUnorientedVerticalWindingTotal pairing / 2 := by
-- proof
  apply StatMech.FrontierD.le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul pairing arrows hcompat r hflux

/--
[fkOrientedLoopPairingWeight_ne_zero_iff_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedLoopPairingWeight_ne_zero_iff_compatible_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T} :
-- imply
  fkOrientedLoopPairingWeight lam pairing arrows ≠ 0 ↔ ∀ v, fkLoopPairingCompatible (pairing v) arrows v := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopPairingWeight_ne_zero_iff_compatible lam pairing arrows

/--
[fkOrientedLoopPairingWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma fkOrientedLoopPairingWeight_nonneg_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T}
  {arrows : SixVertexArrows T} :
-- imply
  0 ≤ fkOrientedLoopPairingWeight lam pairing arrows := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopPairingWeight_nonneg lam pairing arrows

/--
[exists_positive_weight_verticalFlux_eq_neg_two_mul_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean)
-/
@[path]
private lemma exists_positive_weight_verticalFlux_eq_neg_two_mul_half_eq
  {T : EvenTorus}
  {lam : Real}
  {pairing : FKMedialLoopPairing T} :
-- imply
  ∃ arrows : SixVertexArrows T, 0 < fkOrientedLoopPairingWeight lam pairing arrows ∧ fkOrientedLoopVerticalFlux T arrows = -(2 * ((fkMedialUnorientedVerticalWindingTotal pairing / 2 : Nat) : Int)) := by
-- proof
  apply StatMech.FrontierD.exists_positive_weight_verticalFlux_eq_neg_two_mul_half lam pairing


-- created on 2026-10-23

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Lemma.Definitions.Def_FLTPrelim_GaloisRep

set_option autoImplicit false

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

def InZeroComponentAt (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) : Prop :=
  P = 0 ∨ ∃ (x y : AlgebraicClosure ℚ)
      (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
    P = .some x y h ∧
      (x ∉ A ∨ ∃ (hx : x ∈ A) (hy : y ∈ A),
        (W.map (Int.castRingHom (IsLocalRing.ResidueField A))).toAffine.Nonsingular
          (IsLocalRing.residue A ⟨x, hx⟩) (IsLocalRing.residue A ⟨y, hy⟩))

end WeierstrassCurve

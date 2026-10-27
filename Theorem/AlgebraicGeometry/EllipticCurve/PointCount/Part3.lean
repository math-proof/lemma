import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Def.AlgebraicGeometry.EllipticCurve.PointCount.Part4
open Polynomial

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/


namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

variable {F : Type u} [Field F]

variable (W : Affine F)

/-- A Weierstrass equation over a finite field has at most two affine points over each
`x`-coordinate, plus the point at infinity. -/
theorem natCard_point_le_two_mul_natCard_add_one [Finite F] :
    Nat.card W.Point ≤ 2 * Nat.card F + 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  let encode : W.Point → Option {xy : Prod F F // W.Equation xy.1 xy.2}
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  have hinj : Function.Injective encode := by
    intro P Q h
    cases P <;> cases Q <;> simp_all [encode]
  calc
    Nat.card W.Point ≤ Nat.card (Option {xy : Prod F F // W.Equation xy.1 xy.2}) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 :=
      Finite.card_option
    _ =
        (∑ x : F, Nat.card {y : F // W.Equation x y}) + 1 := by
      rw [Nat.card_congr (affineSolutionsEquivSigma W), Nat.card_sigma]
    _ ≤ (∑ _x : F, 2) + 1 := by
      gcongr with x
      exact equationFiber_natCard_le_two W x
    _ = 2 * Nat.card F + 1 := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- The point-count formula rearranged as `#E(𝔽_q) = q + 1 - a_q(E)`. -/
theorem natCard_point_eq_natCard_add_one_sub_frobeniusTrace [Finite F] :
    (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace := by
  rw [frobeniusTrace]
  ring

/-- The point count and Frobenius trace sum to `q + 1`. -/
theorem natCard_point_add_frobeniusTrace_eq [Finite F] :
    (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 := by
  rw [frobeniusTrace]
  ring

end WeierstrassCurve.Affine

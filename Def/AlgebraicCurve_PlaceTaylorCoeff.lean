import Mathlib
import Def.AlgebraicCurve_PlaceEvaluation

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

def taylorRem (v : Place K F) (t f : F) : ℕ → F
  | 0 => f
  | r + 1 => (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹

def taylorCoeff (v : Place K F) (t : F) (r : ℕ) (f : F) : K :=
  v.evalAt (taylorRem v t f r)

variable (v : Place K F) (t f : F)

@[simp]
theorem taylorRem_zero : taylorRem v t f 0 = f := rfl

theorem taylorCoeff_zero : taylorCoeff v t 0 f = v.evalAt f := rfl


end Place

def jetMatrix {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (f j)

theorem jetMatrix_order_zero {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F)
    (f : Fin M → F) :
    jetMatrix P t (fun _ => 0) f = Matrix.of fun i j => (P i).evalAt (f j) := rfl

open Classical in

def jetMult {M : ℕ} (P : Fin M → Place K F) (v : Place K F) : ℕ :=
  (Finset.univ.filter fun i => P i = v).card

def jetDivisor {M : ℕ} (P : Fin M → Place K F) : Divisor K F :=
  ∑ i, Finsupp.single (P i) 1


def IsConfluentPattern {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ) :
    Prop :=
  (∀ i i', P i = P i' → t i = t i') ∧
  (∀ i i', P i = P i' → e i = e i' → i = i') ∧
  (∀ i, e i < jetMult P (P i))

end AlgebraicCurve

end

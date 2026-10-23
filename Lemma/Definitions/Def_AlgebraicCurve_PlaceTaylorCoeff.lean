import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation

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

theorem taylorRem_succ (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (v.evalAt (taylorRem v t f r))) * t⁻¹ := rfl

@[simp]
theorem taylorCoeff_zero : taylorCoeff v t 0 f = v.evalAt f := rfl

theorem taylorCoeff_eq (r : ℕ) : taylorCoeff v t r f = v.evalAt (taylorRem v t f r) := rfl

theorem taylorRem_succ' (r : ℕ) :
    taylorRem v t f (r + 1)
      = (taylorRem v t f r - algebraMap K F (taylorCoeff v t r f)) * t⁻¹ := rfl

theorem taylorRem_eq_add_mul_succ {t : F} (ht : t ≠ 0) (f : F) (r : ℕ) :
    taylorRem v t f r
      = algebraMap K F (taylorCoeff v t r f) + t * taylorRem v t f (r + 1) := by
  rw [taylorRem_succ', mul_comm _ t⁻¹, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  abel

theorem eq_sum_taylorCoeff_mul_pow_add_pow_mul_taylorRem {t : F} (ht : t ≠ 0) (f : F) (n : ℕ) :
    f = (∑ q ∈ Finset.range n, algebraMap K F (taylorCoeff v t q f) * t ^ q)
        + t ^ n * taylorRem v t f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nth_rewrite 1 [ih]
    rw [taylorRem_eq_add_mul_succ v ht f n]
    ring

end Place

def jetMatrix {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (f j)

theorem jetMatrix_apply {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (f : Fin M → F) (i j : Fin M) :
    jetMatrix P t e f i j = (P i).taylorCoeff (t i) (e i) (f j) := rfl

@[simp]
theorem jetMatrix_order_zero {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F)
    (f : Fin M → F) :
    jetMatrix P t (fun _ => 0) f = Matrix.of fun i j => (P i).evalAt (f j) := rfl

open Classical in

def jetMult {M : ℕ} (P : Fin M → Place K F) (v : Place K F) : ℕ :=
  (Finset.univ.filter fun i => P i = v).card

def jetDivisor {M : ℕ} (P : Fin M → Place K F) : Divisor K F :=
  ∑ i, Finsupp.single (P i) 1

theorem jetDivisor_apply {M : ℕ} (P : Fin M → Place K F) (v : Place K F) :
    jetDivisor P v = (jetMult P v : ℤ) := by
  classical
  simp only [jetDivisor, jetMult, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_boole]

def IsConfluentPattern {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ) :
    Prop :=
  (∀ i i', P i = P i' → t i = t i') ∧
  (∀ i i', P i = P i' → e i = e i' → i = i') ∧
  (∀ i, e i < jetMult P (P i))

end AlgebraicCurve

end

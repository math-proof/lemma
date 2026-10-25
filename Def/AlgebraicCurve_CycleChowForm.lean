import Def.AlgebraicCurve_ChordalProximity

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

def linSec {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (a : Fin r → AlgebraicClosure ℚ) : F :=
  ∑ i, a i • s i

def chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (Z : Divisor (AlgebraicClosure ℚ) F) : MvPolynomial (Fin r) (AlgebraicClosure ℚ) :=
  Z.prod fun w n => (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i) ^ n.toNat

def secProd {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F) (k : ℕ)
    (u : F) (Z : Divisor (AlgebraicClosure ℚ) F) : AlgebraicClosure ℚ :=
  Z.prod fun w n => secVal s w k u ^ n.toNat

def chowLogAt {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (ν : AlgebraicClosure ℚ → ℝ)
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  Real.log (⨆ a : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0},
    ν (MvPolynomial.eval a.1 (chowForm s Z)) / (⨆ i, ν (a.1 i)) ^ (Z.sum fun _ n => n.toNat))

def chowSide {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (ν : AlgebraicClosure ℚ → ℝ)
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  (Z.sum fun w n => (n : ℝ) * Real.log (⨆ i, ν (evalVec s w i))) - chowLogAt ν s Z v

def ChowReciprocity {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (E : Divisor (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) (B : Divisor (AlgebraicClosure ℚ) F) : Prop :=
  ∀ (a b c : Fin r → AlgebraicClosure ℚ) (Za Zb Zc : Divisor (AlgebraicClosure ℚ) F),
    linSec s a ≠ 0 → linSec s b ≠ 0 → linSec s c ≠ 0 →
    (∀ w, Za w = w.ord (linSec s a) + E w) → (∀ w, Zb w = w.ord (linSec s b) + E w) →
    (∀ w, Zc w = w.ord (linSec s c) + E w) →
    (∀ w, (Za w = 0 ∧ Zb w = 0) ∨ (B w = 0 ∧ Zc w = 0)) →
    MvPolynomial.eval a (chowForm s B) * MvPolynomial.eval b (chowForm s Zc) ^ k
        * MvPolynomial.eval c (chowForm s Za) ^ k * secProd s k u Zb
      = MvPolynomial.eval b (chowForm s B) * MvPolynomial.eval a (chowForm s Zc) ^ k
        * MvPolynomial.eval c (chowForm s Zb) ^ k * secProd s k u Za

@[simp]
theorem chowForm_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) : chowForm s 0 = 1 :=
  Finsupp.prod_zero_index


theorem secProd_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (k : ℕ) (u : F) : secProd s k u 0 = 1 :=
  Finsupp.prod_zero_index


end AlgebraicCurve

end

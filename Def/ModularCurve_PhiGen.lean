module

public import Theorem.HahnSeries.X0
public import Theorem.LaurentSeries.LaurentCoeff
public import Mathlib.Algebra.Polynomial.BigOperators
public import Abbrev.ModularCurve_PhiGen

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology
open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve

section QTwist

variable {R : Type*} [CommRing R]

def qTwistFun (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R where
  coeff k := (u ^ k : Rˣ) * f.coeff k
  isPWO_support' := f.isPWO_support'.mono fun k hk => by
    simp only [Function.mem_support] at hk ⊢
    exact fun h => hk (by rw [h, mul_zero])

open Finset renaming antidiagonal → pwoAntidiagonal, mem_antidiagonal → mem_pwoAntidiagonal in
def qTwist (u : Rˣ) : LaurentSeries R →+* LaurentSeries R where
  toFun := qTwistFun u
  map_one' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_one]
    split_ifs with h
    · subst h; simp
    · rw [mul_zero]
  map_mul' f g := by
    ext k

    have hset : pwoAntidiagonal (qTwistFun u f).isPWO_support
        (qTwistFun u g).isPWO_support k =
        pwoAntidiagonal f.isPWO_support g.isPWO_support k := by
      ext ij
      simp only [mem_pwoAntidiagonal, support_qTwistFun]
    rw [qTwistFun_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, hset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    obtain ⟨-, -, hsum⟩ := mem_pwoAntidiagonal.mp hij
    rw [qTwistFun_coeff, qTwistFun_coeff, mul_mul_mul_comm, ← Units.val_mul, ← zpow_add,
      hsum]
  map_zero' := by
    ext k
    rw [qTwistFun_coeff, HahnSeries.coeff_zero, mul_zero]
  map_add' f g := by
    ext k
    rw [HahnSeries.coeff_add]
    show (qTwistFun u (f + g)).coeff k = (qTwistFun u f).coeff k + (qTwistFun u g).coeff k
    rw [qTwistFun_coeff, qTwistFun_coeff, qTwistFun_coeff, HahnSeries.coeff_add, mul_add]

end QTwist

section CosetSubst

variable {K : Type*} [Field K]

def cosetSubst (ζ : Kˣ) (a b : ℕ) [NeZero a] : LaurentSeries K →+* LaurentSeries K :=
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  (qExpand K (a * a)).comp (qTwist (ζ ^ (a * b)))

end CosetSubst

section EvalAtJqN

variable (N : ℕ) [NeZero N]

def evalAtJqN : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) (jqN N)).toRingHom

end EvalAtJqN

section Symmetry

def EvalSymm (Φ : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ x y : LaurentSeries ℚ,
    Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom x

end Symmetry

def PoleOrderLE (f : LaurentSeries ℚ) (n : ℕ) : Prop :=
  ∀ k : ℤ, k < -(n : ℤ) → f.coeff k = 0

def ModularPolynomialFamily : Prop :=
  ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ

section Named

variable {N : ℕ} [NeZero N]

def PhiIrreducible (data : ModularPolynomialData N) : Prop :=
  Irreducible data.toAdjoin

end Named

section AdjoinRing

def jAdj : adjoinJq := ⟨jq, Algebra.self_mem_adjoin_singleton ℚ jq⟩

def evalAtJAdj : Polynomial ℤ →+* adjoinJq :=
  Polynomial.eval₂RingHom (Int.castRingHom adjoinJq) jAdj

end AdjoinRing

section SwapBivar

def swapInner : Polynomial ℤ →+* Polynomial (Polynomial ℤ) :=
  (Polynomial.aeval (R := ℤ) (Polynomial.X : Polynomial (Polynomial ℤ))).toRingHom

def swapBivar : Polynomial (Polynomial ℤ) →+* Polynomial (Polynomial ℤ) :=
  Polynomial.eval₂RingHom swapInner (Polynomial.C Polynomial.X)

end SwapBivar

namespace PhiGen

section CosetIndex

variable (ℓ : ℕ)

def cosetA (i : Fin (ℓ + 1)) : ℕ := if i = 0 then ℓ else 1

def cosetB (i : Fin (ℓ + 1)) : ℕ := if i = 0 then 0 else (i : ℕ) - 1

end CosetIndex

section ConjugateFamily

variable {K : Type*} [Field K]

variable [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

def conj (i : Fin (ℓ + 1)) : LaurentSeries K :=
  cosetSubst ζ (cosetA ℓ i) (cosetB ℓ i) (coeffEmb K jq)

end ConjugateFamily

section Product

variable {K : Type*} [Field K] (ℓ : ℕ)

def phiProd (conj : Fin (ℓ + 1) → LaurentSeries K) : Polynomial (LaurentSeries K) :=
  ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conj i))

end Product

section PoleDefs

variable {K : Type*} [Field K]

def TPoleOrderLE (f : LaurentSeries K) (n : ℕ) : Prop :=
  ∀ m : ℤ, m < -(n : ℤ) → f.coeff m = 0

variable (J : LaurentSeries K)

def JSimplePole : Prop := ∀ m : ℤ, m < -1 → J.coeff m = 0

end PoleDefs

def IntCoeffs (f : LaurentSeries ℚ) : Prop :=
  ∀ m : ℤ, ∃ z : ℤ, f.coeff m = (z : ℚ)

section Descends

variable {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

def PhiGenDescends (c : ℕ → LaurentSeries ℚ) : Prop :=
  ∀ k : ℕ, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))

end Descends

end PhiGen

end ModularCurve

end

end

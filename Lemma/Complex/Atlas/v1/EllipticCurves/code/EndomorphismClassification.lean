import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.Theorem136.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem136
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
open OrdinarySupersingular EndomorphismRingOverFiniteField


/--
[even_of_sq_eq_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismClassification.lean)
-/
@[path]
lemma even_of_sq_eq_prime_pow
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  ∀ n k : ℕ, k ^ 2 = p ^ n → Even n := by
-- proof
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro k hk
    match n with
    | 0 => exact ⟨0, by omega⟩
    | 1 =>
      exfalso
      simp [pow_one] at hk
      exact Irreducible.not_isSquare hp ⟨k, by rw [← hk]; ring⟩
    | n + 2 =>
      have hpk2 : p ∣ k ^ 2 := ⟨p ^ (n + 1), by rw [hk]; ring⟩
      have hpk : p ∣ k := hp.dvd_of_dvd_pow hpk2
      obtain ⟨j, rfl⟩ := hpk
      have hpn : j ^ 2 = p ^ n := by
        have h1 : (p * j) ^ 2 = p ^ (n + 2) := hk
        have h2 : p ^ 2 * j ^ 2 = p ^ 2 * p ^ n := by
          have : p * p * (j * j) = p * p * p ^ n := by
            calc p * p * (j * j) = (p * j) * (p * j) := by ring
            _ = (p * j) ^ 2 := by ring
            _ = p ^ (n + 2) := h1
            _ = p * p * p ^ n := by ring
          linarith
        exact Nat.eq_of_mul_eq_mul_left
          (Nat.pos_of_ne_zero (pow_ne_zero 2 hp.ne_zero)) h2
      have heven := ih n (by omega) j hpn
      obtain ⟨m, rfl⟩ := heven
      exact ⟨m + 1, by omega⟩

/--
[even_of_int_sq_eq_four_mul_prime_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismClassification.lean)
-/
@[path]
lemma even_of_int_sq_eq_four_mul_prime_pow
  {p : ℕ}
  {n : ℕ}
  {t : ℤ}
-- given
  (hp : Nat.Prime p)
  (h : t ^ 2 = 4 * (p ^ n : ℤ)) :
-- imply
  Even n := by
-- proof
  have heven_t : 2 ∣ t := by
    have heven_sq : Even (t ^ 2) := ⟨2 * (p ^ n : ℤ), by omega⟩
    rw [Int.even_pow] at heven_sq
    exact even_iff_two_dvd.mp heven_sq.1
  obtain ⟨k, rfl⟩ := heven_t
  have hk2 : k ^ 2 = (p : ℤ) ^ n := by nlinarith
  have hnat : (k.natAbs) ^ 2 = p ^ n := by
    have h1 : ((k.natAbs : ℤ) ^ 2 : ℤ) = k ^ 2 := Int.natAbs_sq k
    have h2 : ((k.natAbs ^ 2 : ℕ) : ℤ) = (k.natAbs : ℤ) ^ 2 := by push_cast; ring
    have h3 : ((p ^ n : ℕ) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    exact_mod_cast (show ((k.natAbs ^ 2 : ℕ) : ℤ) = ((p ^ n : ℕ) : ℤ) by
      rw [h2, h1, hk2, h3])
  exact even_of_sq_eq_prime_pow p hp n k.natAbs hnat
open OrdinarySupersingular EndomorphismRingOverFiniteField
section Corollary137_EC
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/--
[frobeniusNotInt_of_odd_or_ordinary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismClassification.lean)
-/
@[path]
lemma frobeniusNotInt_of_odd_or_ordinary
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [CharP F p]
  {n : ℕ}
  {E : WeierstrassCurve.Affine F}
-- given
  (hcard : Fintype.card F = p ^ n)
  (h : Odd n ∨ IsOrdinary E p) :
-- imply
  frobeniusNotInt E := by
-- proof
  intro hnotint
  rw [hcard] at hnotint
  have heven : Even n :=
    even_of_int_sq_eq_four_mul_prime_pow p hp.out n _ (by push_cast at hnotint ⊢; exact hnotint)
  have htrace_dvd : (p : ℤ) ∣ Hasse.traceFrobenius E := by
    obtain ⟨m, rfl⟩ := heven
    have hcard_pos : 0 < Fintype.card F := Fintype.card_pos
    rw [hcard] at hcard_pos
    have hp_pos : 1 < p := hp.out.one_lt
    have hm_pos : 0 < m + m := by
      by_contra hle
      simp only [not_lt, Nat.le_zero] at hle
      have hm0 : m = 0 := by omega
      subst hm0
      simp at hcard
      have : 1 < Fintype.card F := Fintype.one_lt_card
      omega
    have hm1 : 1 ≤ m := by omega
    push_cast at hnotint
    have hsq : (Hasse.traceFrobenius E) ^ 2 = (2 * (p : ℤ) ^ m) ^ 2 := by
      rw [hnotint]; ring
    have habs : Hasse.traceFrobenius E = 2 * (p : ℤ) ^ m ∨
      Hasse.traceFrobenius E = -(2 * (p : ℤ) ^ m) :=
      sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    have hpm : (p : ℤ) ∣ (p : ℤ) ^ m := dvd_pow_self (p : ℤ) (by omega : m ≠ 0)
    obtain heq | heq <;> rw [heq] := habs
    · exact dvd_mul_of_dvd_right hpm 2
    · exact dvd_neg.mpr (dvd_mul_of_dvd_right hpm 2)
  have hsuper : IsSupersingular E p :=
    (isSupersingular_iff_trace_dvd p E).mpr htrace_dvd
  obtain hodd | hord := h
  · exact absurd hodd (Nat.not_odd_iff_even.mpr heven)
  · exact (isOrdinary_iff_not_supersingular E p).mp hord hsuper

/--
[endAlg_imagQuad_of_ordinary_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismClassification.lean)
-/
@[path]
lemma endAlg_imagQuad_of_ordinary_or_odd
  [Field F]
  [Fintype F]
  [DecidableEq F]
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [CharP F p]
  {n : ℕ}
  {E : WeierstrassCurve.Affine F}
-- given
  (hcard : Fintype.card F = p ^ n)
  (h : Odd n ∨ IsOrdinary E p) :
-- imply
  frobeniusDiscriminant E < 0 ∧ Module.finrank ℚ (EllipticCurve.EndAlgebra E) = 2 ∧ ∃ α : EllipticCurve.EndAlgebra E, (∀ q : ℚ, α ≠ (algebraMap ℚ (EllipticCurve.EndAlgebra E)) q) ∧ ∃ d : ℚ, d < 0 ∧ α * α = (algebraMap ℚ (EllipticCurve.EndAlgebra E)) d := by
-- proof
  have hnotint := frobeniusNotInt_of_odd_or_ordinary p n hcard E h
  have hq : 0 < Fintype.card F := Fintype.card_pos
  exact ⟨frobeniusDiscriminant_neg E hq hnotint,
    endAlg_finrank_eq_two E hq hnotint,
    endAlg_has_imaginary_generator E hq hnotint⟩
end Corollary137_EC


-- created on 2026-10-23

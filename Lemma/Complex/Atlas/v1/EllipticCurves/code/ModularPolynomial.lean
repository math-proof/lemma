import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.ModularPolynomial
open CongruenceSubgroup Complex ModularFunction ExtendedUpperHalfPlane
open scoped MatrixGroups UpperHalfPlane
open ModularFunction
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
open Polynomial hiding C X coeff_zero
open ModularFunctionField
open ModularGroup


namespace ModularFunction

/--
[jModular_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma jModular_surjective
-- imply
  Function.Surjective jModular :=
-- proof
  jFunction_surjective

end ModularFunction

/--
[coe_S_mul_T_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma coe_S_mul_T_zpow
  {k : ℤ} :
-- imply
  ((S * T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, k] := by
-- proof
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_S, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/--
[coe_S_T_zpow_S_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma coe_S_T_zpow_S_inv
  {m : ℤ} :
-- imply
  ((S * T ^ m * S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
-- proof
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_S, coe_T_zpow, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/--
[product_matrix_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma product_matrix_eq
  {a b c d k : ℤ} :
-- imply
  !![(k * a - b : ℤ), a; (k * c - d : ℤ), c] * (!![(0 : ℤ), -1; 1, k] : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
-- proof
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/--
[gamma0_right_coset_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma gamma0_right_coset_cover
  {N : ℕ}
  {γ : SL(2, ℤ)}
-- given
  (hN : Nat.Prime N) :
-- imply
  γ ∈ CongruenceSubgroup.Gamma0 N ∨ ∃ (k : ℕ) (_ : k < N) (γ₀ : SL(2, ℤ)), γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ = γ₀ * (S * T ^ (k : ℤ)) := by
-- proof
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set c := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set a := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  have hdet : a * d - b * c = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  by_cases hc : (↑c : ZMod N) = 0
  · left; rwa [CongruenceSubgroup.Gamma0_mem]
  · right
    set k := ZMod.val ((↑d : ZMod N) * (↑c : ZMod N)⁻¹)
    have hk_lt : k < N := ZMod.val_lt _
    have hkc : (↑k : ZMod N) * (↑c : ZMod N) = (↑d : ZMod N) := by
      show (↑(ZMod.val ((↑d : ZMod N) * (↑c : ZMod N)⁻¹)) : ZMod N) * _ = _
      rw [ZMod.natCast_val, ZMod.cast_id']
      show (↑d : ZMod N) * (↑c : ZMod N)⁻¹ * (↑c : ZMod N) = (↑d : ZMod N)
      rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
    have hkcd : (↑((↑k : ℤ) * c - d) : ZMod N) = 0 := by
      push_cast; exact sub_eq_zero.mpr hkc
    have hdet₀ : ((↑k : ℤ) * a - b) * c - a * ((↑k : ℤ) * c - d) = 1 := by linarith
    set γ₀ : SL(2, ℤ) := ⟨!![(↑k : ℤ) * a - b, a; (↑k : ℤ) * c - d, c],
      by rw [Matrix.det_fin_two]; simpa using hdet₀⟩
    refine ⟨k, hk_lt, γ₀, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma0_mem]; exact hkcd
    · apply Subtype.ext
      show (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ₀ : Matrix (Fin 2) (Fin 2) ℤ) *
        ((S * T ^ (↑k : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      rw [coe_S_mul_T_zpow]
      have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hγ, show (γ₀ : Matrix _ _ ℤ) =
        !![(↑k : ℤ) * a - b, a; (↑k : ℤ) * c - d, c] from rfl]
      exact (product_matrix_eq a b c d ↑k).symm

/--
[S_mul_T_zpow_not_mem_gamma0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma S_mul_T_zpow_not_mem_gamma0
  {N : ℕ}
  {k : ℤ}
-- given
  (hN : Nat.Prime N) :
-- imply
  S * T ^ k ∉ CongruenceSubgroup.Gamma0 N := by
-- proof
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  intro hmem; rw [CongruenceSubgroup.Gamma0_mem] at hmem
  have : ((S * T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [coe_S_mul_T_zpow]; simp
  rw [this] at hmem; simp at hmem

/--
[gamma0_coset_distinct_neq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma gamma0_coset_distinct_neq
  {N : ℕ}
  {j k : ℕ}
-- given
  (hN : Nat.Prime N)
  (hj : j < N)
  (hk : k < N)
  (hjk : j ≠ k) :
-- imply
  (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ ∉ CongruenceSubgroup.Gamma0 N := by
-- proof
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  rw [show (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ =
    S * T ^ ((k : ℤ) - j) * S⁻¹ from by group]
  intro hmem; rw [CongruenceSubgroup.Gamma0_mem] at hmem
  have : ((S * T ^ ((k : ℤ) - j) * S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
    -((k : ℤ) - j) := by rw [coe_S_T_zpow_S_inv]; simp
  rw [this] at hmem
  simp only [Int.cast_neg, neg_eq_zero, Int.cast_sub, Int.cast_natCast] at hmem
  exact hjk (by
    have := congr_arg ZMod.val (sub_eq_zero.mp hmem)
    rw [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hj] at this
    omega)

/--
[lemma_19_16](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
lemma lemma_19_16
  {N : ℕ}
-- given
  (hN : Nat.Prime N) :
-- imply
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N ∨ ∃ (k : ℕ) (_ : k < N) (γ₀ : SL(2, ℤ)), γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ = γ₀ * (S * T ^ (k : ℤ))) ∧ (∀ k : ℤ, S * T ^ k ∉ CongruenceSubgroup.Gamma0 N) ∧ (∀ j k : ℕ, j < N → k < N → j ≠ k → (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ ∉ CongruenceSubgroup.Gamma0 N) :=
-- proof
  ⟨gamma0_right_coset_cover N hN,
    S_mul_T_zpow_not_mem_gamma0 N hN,
    gamma0_coset_distinct_neq N hN⟩
namespace ModularPolynomial

/--
[sl2zEntry_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma sl2zEntry_det_eq
  {γ : SL(2, ℤ)} :
-- imply
  sl2zEntry γ 0 0 * sl2zEntry γ 1 1 - sl2zEntry γ 0 1 * sl2zEntry γ 1 0 = 1 := by
-- proof
  apply sl2zEntry_det γ

/--
[sl2zEntry_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma sl2zEntry_mul_eq
  {g₁ g₂ : SL(2, ℤ)}
  {i j : Fin 2} :
-- imply
  sl2zEntry (g₁ * g₂) i j = sl2zEntry g₁ i 0 * sl2zEntry g₂ 0 j + sl2zEntry g₁ i 1 * sl2zEntry g₂ 1 j := by
-- proof
  apply sl2zEntry_mul g₁ g₂ i j

/--
[cuspAction_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_one_eq :
-- imply
  ∀ x, cuspAction 1 x = x := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_one

/--
[cuspAction_factor_denom_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_factor_denom_zero_eq
  {g₁ g₂ : SL(2, ℤ)}
  {r : ℚ}
-- given
  (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
-- imply
  sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_factor_denom_zero g₁ g₂ r hd₂

/--
[cuspAction_factor_numer_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_factor_numer_zero_eq
  {g₁ g₂ : SL(2, ℤ)}
  {r : ℚ}
-- given
  (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
-- imply
  sl2zEntry (g₁ * g₂) 0 0 * r + sl2zEntry (g₁ * g₂) 0 1 = sl2zEntry g₁ 0 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_factor_numer_zero g₁ g₂ r hd₂

/--
[cuspAction_numer_ne_zero_of_denom_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_numer_ne_zero_of_denom_zero_eq
  {g₂ : SL(2, ℤ)}
  {r : ℚ}
-- given
  (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
-- imply
  sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1 ≠ 0 := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_numer_ne_zero_of_denom_zero g₂ r hd₂

/--
[cuspAction_mul_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_mul_top_eq
  {g₁ g₂ : SL(2, ℤ)} :
-- imply
  cuspAction (g₁ * g₂) ⊤ = cuspAction g₁ (cuspAction g₂ ⊤) := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_mul_top g₁ g₂

/--
[cuspAction_mul_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_mul_coe_eq
  {g₁ g₂ : SL(2, ℤ)}
  {r : ℚ} :
-- imply
  cuspAction (g₁ * g₂) ↑r = cuspAction g₁ (cuspAction g₂ ↑r) := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_mul_coe g₁ g₂ r

/--
[cuspAction_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean)
-/
@[path]
private lemma cuspAction_mul_eq
  {g₁ g₂ : SL(2, ℤ)} :
-- imply
  ∀ x, cuspAction (g₁ * g₂) x = cuspAction g₁ (cuspAction g₂ x) := by
-- proof
  apply ExtendedUpperHalfPlane.cuspAction_mul g₁ g₂


-- created on 2026-10-23

import Mathlib
import sympy.Basic


/--
[Matrix_exists_det_map_eq_of_isUnit_of_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_det_map_eq_of_isUnit_of_ne.lean)
-/
@[path]
private lemma main
  {ℓ q : ℕ} [Fact ℓ.Prime] [Fact q.Prime]
  {u : (ZMod ℓ)ˣ}
  {v : (ZMod q)ˣ}
-- given
  (hℓq : ℓ ≠ q) :
-- imply
  ∃ g : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit (g.map (Int.castRingHom (ZMod (q * ℓ)))).det ∧
      ((g.det : ℤ) : ZMod ℓ) = (u : ZMod ℓ) ∧ ((g.det : ℤ) : ZMod q) = (v : ZMod q) := by
-- proof
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hco : Nat.Coprime ℓ q := (Nat.coprime_primes Fact.out Fact.out).mpr hℓq
  obtain ⟨d, hdℓ, hdq⟩ := Nat.chineseRemainder hco (u : ZMod ℓ).val (v : ZMod q).val
  have hdℓ' : (d : ZMod ℓ) = (u : ZMod ℓ) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdℓ, ZMod.natCast_zmod_val]
  have hdq' : (d : ZMod q) = (v : ZMod q) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hdq, ZMod.natCast_zmod_val]
  have hcoℓ : Nat.Coprime d ℓ := by
    rw [Nat.coprime_iff_gcd_eq_one, hdℓ.gcd_eq]
    exact ZMod.val_coe_unit_coprime u
  have hcoq : Nat.Coprime d q := by
    rw [Nat.coprime_iff_gcd_eq_one, hdq.gcd_eq]
    exact ZMod.val_coe_unit_coprime v
  refine ⟨!![(d : ℤ), 0; 0, 1], ?_, ?_, ?_⟩
  · have hdet : (Matrix.map !![(d : ℤ), 0; 0, 1] (Int.castRingHom (ZMod (q * ℓ)))).det =
        ((d : ℕ) : ZMod (q * ℓ)) := by
      simp [Matrix.det_fin_two]
    rw [hdet, ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.mul_right hcoq hcoℓ
  · simp [Matrix.det_fin_two, hdℓ']
  · simp [Matrix.det_fin_two, hdq']


-- created on 2026-10-05

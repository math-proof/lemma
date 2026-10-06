import Mathlib
import sympy.Basic


/--
[RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X.lean)
-/
@[main]
private lemma main
  {p : ℕ}
  {k : Type v} [CommRing k] [Nontrivial k]
  {R : Type u} [CommRing R]
  {a b : R}
-- given
  (hp : 2 ≤ p)
  (e₀ e₁ : R ≃+* Polynomial k)
  (h₀a : e₀ a = Polynomial.X)
  (h₀b : e₀ b = Polynomial.X ^ p)
  (h₁b : e₁ b = Polynomial.X)
  (h₁a : e₁ a = Polynomial.X ^ p) :
-- imply
  False := by
-- proof
  have ha : e₀.symm Polynomial.X = a := by rw [← h₀a, e₀.symm_apply_apply]
  have hb : e₀.symm (Polynomial.X ^ p) = b := by rw [← h₀b, e₀.symm_apply_apply]
  have h1 : (e₀.symm.trans e₁) (Polynomial.X ^ p) = Polynomial.X := by
    rw [RingEquiv.trans_apply, hb, h₁b]
  have h2 : (e₀.symm.trans e₁) (Polynomial.X ^ p) = Polynomial.X ^ (p * p) := by
    rw [map_pow, RingEquiv.trans_apply, ha, h₁a, ← pow_mul]
  have h3 := congrArg Polynomial.natDegree (h1.symm.trans h2)
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow] at h3
  have h4 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp hp
  omega


-- created on 2026-10-05

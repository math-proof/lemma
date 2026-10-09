import Mathlib
import sympy.Basic


/--
[Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_isUnit_of_isUnit_map_of_le_jacobson_bot.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S]
  {n : Type v} [Fintype n] [DecidableEq n]
  {𝔫 : Ideal S}
  {A : Matrix n n S}
-- given
  (h𝔫 : 𝔫 ≤ (⊥ : Ideal S).jacobson)
  (hA : IsUnit (A.map (Ideal.Quotient.mk 𝔫))) :
-- imply
  IsUnit A := by
-- proof
  rw [Matrix.isUnit_iff_isUnit_det] at hA ⊢
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hA

  obtain ⟨b, hb⟩ := hA.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔫), Ideal.Quotient.eq] at hb
  have hu : IsUnit (A.det * b) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ (h𝔫 hb)
  exact isUnit_of_mul_isUnit_left hu


-- created on 2026-10-05

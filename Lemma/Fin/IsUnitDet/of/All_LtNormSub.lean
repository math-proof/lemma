import Mathlib
import sympy.Basic

open Matrix

/--
[Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_isUnit_det_padicInt_of_norm_sub_one_lt_one.lean)
-/
@[main]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {n : ℕ}
  {P : Matrix (Fin n) (Fin n) ℤ_[p]}
-- given
  (h : ∀ i j, ‖P i j - (1 : Matrix (Fin n) (Fin n) ℤ_[p]) i j‖ < 1) :
-- imply
  IsUnit P.det := by
-- proof
  classical

  have htz : ∀ x : ℤ_[p], ‖x‖ < 1 → (PadicInt.toZMod : ℤ_[p] →+* ZMod p) x = 0 := fun x hx => by
    obtain ⟨y, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd x).mp hx
    rw [map_mul, show ((p : ℤ_[p]) = ((p:ℕ) : ℤ_[p])) from rfl, map_natCast,
        ZMod.natCast_self, zero_mul]

  have hmapeq : (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix P
      = (PadicInt.toZMod : ℤ_[p] →+* ZMod p).mapMatrix (1:Matrix (Fin n) (Fin n) ℤ_[p]) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub]
    exact htz _ (h i j)
  have hdet1 : (PadicInt.toZMod : ℤ_[p] →+* ZMod p) P.det = 1 := by
    rw [RingHom.map_det, hmapeq, map_one, Matrix.det_one]

  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  push_neg at hlt
  exact zero_ne_one (α := ZMod p) ((htz P.det hlt) ▸ hdet1)


-- created on 2026-10-05

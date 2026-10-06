import Mathlib
import sympy.Basic


/--
[Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_exists_isUnit_det_and_mul_map_castRingHom_zmod_eq_one.lean)
-/
@[main]
private lemma main
  [Fintype m] [DecidableEq m]
  {n : ℕ}
  {g : Matrix m m ℤ}
-- given
  (hg : IsUnit ((g.det : ℤ) : ZMod n)) :
-- imply
  ∃ g' : Matrix m m ℤ, IsUnit ((g'.det : ℤ) : ZMod n) ∧
      (g * g').map (Int.castRingHom (ZMod n)) = 1 ∧ (g' * g).map (Int.castRingHom (ZMod n)) = 1 := by
-- proof
  classical
  let f : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  let gb : Matrix m m (ZMod n) := g.map f
  have hfdet : ∀ M : Matrix m m ℤ, ((M.det : ℤ) : ZMod n) = (M.map f).det := by
    intro M
    have h := RingHom.map_det f M
    simpa using h
  have hdet : IsUnit gb.det := by
    rw [show gb.det = ((g.det : ℤ) : ZMod n) from (hfdet g).symm]
    exact hg
  let g' : Matrix m m ℤ := (gb⁻¹).map (ZMod.cast : ZMod n → ℤ)
  have hg' : g'.map f = gb⁻¹ := by
    ext i j
    show f (ZMod.cast (gb⁻¹ i j)) = gb⁻¹ i j
    exact ZMod.intCast_zmod_cast (gb⁻¹ i j)
  refine ⟨g', ?_, ?_, ?_⟩
  · rw [hfdet g', hg']
    exact Matrix.isUnit_nonsing_inv_det gb hdet
  · show (g * g').map f = 1
    rw [Matrix.map_mul, hg']
    exact Matrix.mul_nonsing_inv gb hdet
  · show (g' * g).map f = 1
    rw [Matrix.map_mul, hg']
    exact Matrix.nonsing_inv_mul gb hdet


-- created on 2026-10-05

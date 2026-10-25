/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part9


namespace MetaMathlibExt

lemma r3leg_imageRep_card {p n : ℕ} [Fact (Nat.Prime p)]
    (π : Quaternion ℤ) (hnorm : Quaternion.normSq π = p) :
    (r3legImageRep p n π).card = Nat.threeSquareRepresentationCount n := by
  rw [← r3leg_rep_card]
  symm
  refine Finset.card_bij (fun x _ => r3legPhi π x) ?_ ?_ ?_
  · intro x hx
    rw [r3leg_mem_imageRep]
    have hxq := r3leg_mem_rep.mp hx
    constructor
    · rw [r3leg_q_phi, hnorm, hxq]
      push_cast
      ring
    · rw [r3leg_phi_phi_star, hnorm]
      simp [r3legVecDvd, r3legScale]
  · intro x₁ _ x₂ _ h
    apply r3leg_phi_injective π (by rw [hnorm]; exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    exact h
  · intro y hy
    rw [r3leg_mem_imageRep] at hy
    let x := r3legVecDiv (r3legPhi (star π) y) ((p : ℤ) ^ 2)
    have hscale : r3legScale ((p : ℤ) ^ 2) x = r3legPhi (star π) y := by
      exact r3leg_scale_vecDiv hy.2
    have happly := congrArg (r3legPhi π) hscale
    rw [r3leg_phi_scale, r3leg_phi_star_phi, hnorm] at happly
    have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
      exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
    have hphi : r3legPhi π x = y := r3leg_scale_left_cancel hp2 happly
    have hxq : r3legQ x = (n : ℤ) := by
      have hq := r3leg_q_phi π x
      rw [hphi, hnorm, hy.1] at hq
      push_cast at hq
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
      nlinarith
    refine ⟨x, r3leg_mem_rep.mpr hxq, hphi⟩

end MetaMathlibExt

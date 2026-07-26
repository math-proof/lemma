import Lemma.Hyperreal.Infinite.is.Infinite.of.XEq
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Rat.Eq_0.is.EqInv_0
import Lemma.Rat.InvDiv.eq.Div
open Hyperreal Rat


@[main]
private lemma main
  {x y : ℝ*}
-- given
  (h_not : ¬(x → 0))
  (h : x ≈ y) :
-- imply
  x⁻¹ ≈ y⁻¹ := by
-- proof
  have h_not_y : ¬y → 0 := fun hy => h_not (Infinitesimal.of.Infinitesimal.XEq h.symm hy)
  apply XEq.of.OrAndS
  obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h
  ·
    exfalso
    exact h_not hx
  ·
    if hy_infty : y → ∞ then
      left
      have hx_infty := Infinite.of.Infinite.XEq h.symm hy_infty
      exact ⟨InfinitesimalInv.of.Infinite hx_infty, InfinitesimalInv.of.Infinite hy_infty⟩
    else
      right
      have hx0 := Ne_0.of.NotInfinitesimal h_not
      have hy0 := Ne_0.of.NotInfinitesimal h_not_y
      constructor
      ·
        rw [show x⁻¹ / y⁻¹ - 1 = y / x - 1 by field_simp [hx0]]
        rw [show y / x - 1 = -(x / y - 1) * (y / x) by field_simp [hx0, hy0]; ring]
        apply InfinitesimalMul.of.Infinitesimal.NotInfinite
        ·
          apply InfinitesimalNeg.of.Infinitesimal hxy
        ·
          intro h_yx_infty
          exfalso
          have h_xy_zero : (x / y) → 0 := by
            rw [← InvDiv.eq.Div (a := y) (b := x)]
            exact InfinitesimalInv.of.Infinite h_yx_infty
          have h_neg : (-1 : ℝ*) → 0 := by
            have h_sub := InfinitesimalSub.of.Infinitesimal.Infinitesimal hxy h_xy_zero
            grind
          simp at h_neg
      ·
        intro h_yinv
        have : NeZero y⁻¹ := ⟨NeInv_0.of.Ne_0 hy0⟩
        have hy_infty' : y → ∞ := by
          simpa using InfiniteInv.of.Infinitesimal h_yinv
        exact hy_infty hy_infty'


-- created on 2026-07-26

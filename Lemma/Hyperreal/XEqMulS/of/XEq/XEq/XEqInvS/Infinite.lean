import Lemma.Rat.Eq_0.is.EqInv_0
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Eq_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.Infinite.of.XEq
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.XEq
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_b : b → ∞)
  (h_inv : x⁻¹ ≈ y⁻¹)
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a * x ≈ b * y := by
-- proof
  apply XEq.of.OrAndS
  obtain ⟨ha, hb⟩ | ⟨hab, hb⟩ := OrAndS.of.XEq h₀
  ·
    exfalso
    exact (NotInfinitesimal.of.Infinite h_b) hb
  ·
    obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h₁
    ·
      apply XEq.of.OrAndS
      obtain ⟨h_xinv, h_yinv⟩ | ⟨h_yx, h_yinv_not⟩ := OrAndS.of.XEq h_inv
      ·
        have hx0 : x = 0 := by
          obtain hx0 | hx_ne := eq_or_ne x 0
          · exact hx0
          · exfalso
            have : NeZero x := ⟨hx_ne⟩
            exact (NotInfinite.of.Infinitesimal h_xinv) (InfiniteInv.of.Infinitesimal hx)
        have hy0 : y = 0 := by
          obtain hy0 | hy_ne := eq_or_ne y 0
          · exact hy0
          · exfalso
            have : NeZero y := ⟨hy_ne⟩
            exact (NotInfinite.of.Infinitesimal h_yinv) (InfiniteInv.of.Infinitesimal hy)
        subst hx0 hy0
        left
        simp
      ·
        have ha_infty := Infinite.of.Infinite.XEq h₀.symm h_b
        have hy_ne : y ≠ 0 := by
          intro hy_eq
          subst hy_eq
          exact h_yinv_not (by simp [EqInv_0.of.Eq_0])
        have hx_ne : x ≠ 0 := by
          intro hx_eq
          have h_neg : (-1 : ℝ*) → 0 := by grind
          exact (NotInfinitesimal.of.Ne_0 (r := -1) (by norm_num)) h_neg
        have : NeZero x := ⟨hx_ne⟩
        have : NeZero y := ⟨hy_ne⟩
        have h_yx' : (y / x - 1) → 0 := by
          simpa [div_eq_mul_inv, mul_comm] using h_yx
        have h_st_xy : stdPart (x / y) = 1 := by
          have h_st_yx : stdPart (y / x) = 1 := EqSt.of.InfinitesimalSub h_yx'
          rw [StDiv.eq.InvStInv]
          simp [h_st_yx]
        have h_xy_fin : ¬(x / y) → ∞ := fun h => by
          have := EqSt_0.of.Infinite h
          simp [h_st_xy] at this
        have hxy' : (x / y - 1) → 0 :=
          InfinitesimalSub.of.EqSt.NotInfinite h_xy_fin h_st_xy
        have h_st_ab := EqSt.of.InfinitesimalSub hab
        have ha0' := Ne_0.of.NotInfinitesimal (NotInfinitesimal.of.NotInfinitesimal.XEq h₀ hb)
        have hb0' := Ne_0.of.NotInfinitesimal hb
        have h_ab_fin : ¬(a / b) → ∞ := fun h => by
          have := EqSt_0.of.Infinite h
          simp [h_st_ab] at this
        if h_by0 : (b * y) → 0 then
          left
          have h_ax0 : (a * x) → 0 := by
            have h_eq : a * x = (b * y) * (a / b * (x / y)) := by
              field_simp [hb0', hy_ne, ha0', hx_ne]
            rw [h_eq]
            apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_by0
            exact NotInfiniteMul.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin
          exact ⟨h_ax0, h_by0⟩
        else
          right
          constructor
          ·
            rw [show (a * x) / (b * y) = (a / b) * (x / y) by
              field_simp [hb0', hy_ne, ha0', hx_ne]]
            apply InfinitesimalSub.of.EqSt.NotInfinite
            ·
              exact NotInfiniteMul.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin
            ·
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin]
              simp [h_st_ab, h_st_xy]
          ·
            exact h_by0
    ·
      have h_st_ab := EqSt.of.InfinitesimalSub hab
      have h_st_xy := EqSt.of.InfinitesimalSub hxy
      have h_ab_fin : ¬(a / b) → ∞ := fun h => by
        have := EqSt_0.of.Infinite h
        simp [h_st_ab] at this
      have h_xy_fin : ¬(x / y) → ∞ := fun h => by
        have := EqSt_0.of.Infinite h
        simp [h_st_xy] at this
      have hb0 := Ne_0.of.NotInfinitesimal hb
      have hy0 := Ne_0.of.NotInfinitesimal hy
      if h_zero : b * y = 0 then
        obtain h_b | h_y := OrEqS_0.of.Mul.eq.Zero h_zero
        ·
          subst h_b
          exfalso
          exact hb (by simp)
        ·
          exfalso
          subst h_y
          exact hy (by simp)
      else if h_prod : (b * y) → 0 then
        left
        exfalso
        if h_y_infty : y → ∞ then
          exact (NotInfinite.of.Infinitesimal h_prod) (InfiniteMul.of.Infinite.Infinite h_b h_y_infty)
        else
          exact (NotInfinite.of.Infinitesimal h_prod) (InfiniteMul.of.Infinite.NotInfinitesimal (a := b) (b := y) h_b hy)
      else
        right
        constructor
        ·
          rw [show (a * x) / (b * y) = (a / b) * (x / y) by grind]
          apply InfinitesimalSub.of.EqSt.NotInfinite
          ·
            exact NotInfiniteMul.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin
          ·
            rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin]
            simp [h_st_ab, h_st_xy]
        ·
          exact NotInfinitesimalMul.of.NotInfinitesimal.NotInfinitesimal hb hy


-- created on 2026-07-30

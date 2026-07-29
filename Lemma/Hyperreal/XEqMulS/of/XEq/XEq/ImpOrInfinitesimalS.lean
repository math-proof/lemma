import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalMul.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Nat.Mul.eq.Zero.is.OrEqS_0
open Hyperreal Nat


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_y : (y → ∞) → a⁻¹ ≈ b⁻¹)
  (h_b : (b → ∞) → x⁻¹ ≈ y⁻¹)
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a * x ≈ b * y := by
-- proof
  apply XEq.of.OrAndS
  obtain ⟨ha, hb⟩ | ⟨hab, hb⟩ := OrAndS.of.XEq h₀
  ·
    obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h₁
    ·
      left
      exact ⟨InfinitesimalMul.of.Infinitesimal.Infinitesimal ha hx, InfinitesimalMul.of.Infinitesimal.Infinitesimal hb hy⟩
    ·
      grind
  ·
    obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h₁
    ·
      grind
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
        have h_eq : a * x = (b * y) * (a / b * (x / y)) := by
          field_simp [hb0, hy0]
        if h_y_infty : y → ∞ then
          if h_b_infty : b → ∞ then
            exfalso
            exact (NotInfinite.of.Infinitesimal h_prod) (InfiniteMul.of.Infinite.Infinite h_b_infty h_y_infty)
          else
            exfalso
            have h_by : (b * y) → ∞ := by
              rw [show b * y = y * b by ring]
              exact InfiniteMul.of.Infinite.NotInfinitesimal (a := y) (b := b) h_y_infty hb
            exact (NotInfinite.of.Infinitesimal h_prod) h_by
        else if h_b_infty : b → ∞ then
          exfalso
          exact (NotInfinite.of.Infinitesimal h_prod) (InfiniteMul.of.Infinite.NotInfinitesimal (a := b) (b := y) h_b_infty hy)
        else
          rw [h_eq]
          constructor
          ·
            apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_prod
            exact NotInfiniteMul.of.NotInfinite.NotInfinite h_ab_fin h_xy_fin
          ·
            assumption
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


-- created on 2026-07-25
-- updated on 2026-07-26

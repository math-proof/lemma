import Lemma.Nat.Add
import Lemma.Hyperreal.StAdd.eq.Add_St.of.NotInfinite
import Lemma.Hyperreal.EqSt_0.of.NotInfinite.Infinite
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.Infinite
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Rat.DivMul.eq.Mul_Div
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivDiv.eq.Inv.of.Ne_0
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.St.of.XEq
import Lemma.Hyperreal.StNeg.eq.NegSt
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalAdd.Infinitesimal
import Lemma.Rat.SubDiv.eq.DivSub.of.Ne_0
import sympy.series.limits
open Hyperreal Rat Nat
set_option maxHeartbeats 1000000


@[main]
private lemma main
  {a b x y : ℝ*}
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
  a + x ≈ b + y := by
  apply XEq.of.OrAndS
  obtain ⟨ha, hb⟩ | ⟨hab, hb⟩ := OrAndS.of.XEq h₀
  ·
    obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h₁
    ·
      left
      exact ⟨InfinitesimalAdd.of.Infinitesimal.Infinitesimal ha hx, InfinitesimalAdd.of.Infinitesimal.Infinitesimal hb hy⟩
    ·
      if h : b + y = 0 then
        exfalso
        have : y → 0 := by
          rw [show y = (b + y) - b by ring, h]
          simpa using hb
        exact hy this
      else
        right
        have hyb := NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal hy hb
        constructor
        ·
          rw [Rat.Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
          rw [Rat.DivAdd.eq.AddDivS]
          conv =>
            pattern (b + y) / y
            rw [Rat.DivAdd.eq.AddDivS]
          rw [Rat.Div.eq.One.of.Ne_0 (by grind)]
          have hay := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal ha hy
          have hby := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hb hy
          have h_st_ay := EqSt_0.of.Infinitesimal hay
          have h_st_xy := EqSt.of.InfinitesimalSub hxy
          have h_st_by := EqSt_0.of.Infinitesimal hby
          have h_eq : stdPart ((a / y + x / y) / (b / y + 1)) = (stdPart (a / y) + stdPart (x / y)) / (stdPart (b / y) + 1) := by
            rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal]
            ·
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite
                (NotInfinite.of.Infinitesimal hay) (NotInfinite.of.NeSt_0 (by grind))]
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.AddSt.of.NotInfinite (NotInfinite.of.Infinitesimal hby)]
            ·
              apply NotInfinite.of.NeSt_0
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite
                (NotInfinite.of.Infinitesimal hay) (NotInfinite.of.NeSt_0 (by grind))]
              simp [h_st_ay, h_st_xy]
            ·
              apply NotInfinitesimal.of.NeSt_0
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.AddSt.of.NotInfinite (NotInfinite.of.Infinitesimal hby)]
              simp [h_st_by]
          apply InfinitesimalSub.of.EqSt.NotInfinite
          ·
            by_contra! h
            have h := EqSt_0.of.Infinite h
            simp [h_eq, h_st_ay, h_st_by, h_st_xy] at h
          ·
            simp [h_eq, h_st_ay, h_st_by, h_st_xy]
        ·
          exact hyb
  ·
    obtain ⟨hx, hy⟩ | ⟨hxy, hy⟩ := OrAndS.of.XEq h₁
    ·
      if h : b + y = 0 then
        exfalso
        have : b → 0 := by
          rw [show b = (b + y) - y by ring, h]
          simpa using hy
        exact hb this
      else
        right
        constructor
        ·
          rw [Rat.Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
          rw [Rat.DivAdd.eq.AddDivS]
          conv =>
            pattern (b + y) / b
            rw [Rat.DivAdd.eq.AddDivS]
          rw [Rat.Div.eq.One.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
          conv =>
            pattern (1 + y / b)
            rw [show 1 + y / b = y / b + 1 by ring]
          have hax := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hx hb
          have hxyb := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hy hb
          have h_st_ab := EqSt.of.InfinitesimalSub hab
          have h_st_xb := EqSt_0.of.Infinitesimal hax
          have h_st_yb := EqSt_0.of.Infinitesimal hxyb
          have h_eq : stdPart ((a / b + x / b) / (y / b + 1)) = (stdPart (a / b) + stdPart (x / b)) / (stdPart (y / b) + 1) := by
            rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal]
            ·
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite
                (NotInfinite.of.NeSt_0 (by simp [h_st_ab])) (NotInfinite.of.Infinitesimal hax)]
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.AddSt.of.NotInfinite (NotInfinite.of.Infinitesimal hxyb)]
            ·
              apply NotInfinite.of.NeSt_0
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by simp [h_st_ab])) (NotInfinite.of.Infinitesimal hax)]
              simp [h_st_ab, h_st_xb]
            ·
              apply NotInfinitesimal.of.NeSt_0
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.AddSt.of.NotInfinite (NotInfinite.of.Infinitesimal hxyb)]
              simp [h_st_yb]
          apply InfinitesimalSub.of.EqSt.NotInfinite
          ·
            by_contra! h
            have h := EqSt_0.of.Infinite h
            simp [h_eq, h_st_ab, h_st_xb, h_st_yb] at h
          ·
            simp [h_eq, h_st_ab, h_st_xb, h_st_yb]
        .
          exact NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal.comm hb hy
    ·
      have h_st_ab := Hyperreal.EqSt.of.InfinitesimalSub hab
      have h_st_xy := Hyperreal.EqSt.of.InfinitesimalSub hxy
      have hb0 := Ne_0.of.NotInfinitesimal hb
      have hy0 := Ne_0.of.NotInfinitesimal hy
      if h : (b + y) → 0 then
        simp [h]
        have h_eq : a + x = a / b * b + x / y * y := by
          rw [Rat.EqMulDiv.of.Ne_0 hy0]
          rw [Rat.EqMulDiv.of.Ne_0 hb0]
        rw [h_eq]
        if h_y_infty : y → ∞ then
          if h_b_infty : b → ∞ then
            sorry
          else
            sorry
        else if h_b_infty : b → ∞ then
          sorry
        else
          sorry
      else
        simp [h]
        apply Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
        .
          sorry
        .
          have h_eq : (a + x) / (b + y) = (a / b * b + x / y * y) / (b + y) := by
            rw [Rat.EqMulDiv.of.Ne_0 hy0]
            rw [Rat.EqMulDiv.of.Ne_0 hb0]
          have h_eq' : (a + x) / (b + y) = a / b * (b / (b + y)) + x / y * (y / (b + y))  := by
            rw [h_eq]
            ring
          if h_y_infty : y → ∞ then
            rw [h_eq']
            if h_b_infty : b → ∞ then
              have h_by_finite : ¬(b / (b + y)) → ∞ := by
                sorry
              have h_yb_finite : ¬(y / (b + y)) → ∞ := by
                sorry
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
              .
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
                rw [h_st_ab, h_st_xy]
                simp
                rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
                rw [Rat.AddDivS.eq.DivAdd]
                simp [Div.eq.One.of.Ne_0 (Hyperreal.Ne_0.of.NotInfinitesimal h)]
              .
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
                apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
              .
                apply Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
                apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
            else
              have h_by_finite : ¬(b / (b + y)) → ∞ := by
                apply Hyperreal.NotInfiniteDiv.of.NotInfinite.Infinite _ h_b_infty
                apply Hyperreal.InfiniteAdd.of.Infinite.NotInfinite h_b_infty h_y_infty
              have h_yb_finite : ¬(y / (b + y)) → ∞ := by
                rw [Rat.Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
                rw [DivAdd.eq.AddDivS]
                rw [Rat.Div.eq.One.of.Ne_0 (by grind)]
                apply Hyperreal.NotInfinite.of.NeSt_0
                rw [Div1.eq.Inv]
                rw [Hyperreal.StInv.eq.InvSt]
                apply Rat.NeInv_0.of.Ne_0
                rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
                rw [Hyperreal.StAdd.eq.AddSt.of.NotInfinite (Hyperreal.NotInfiniteDiv.of.NotInfinite.Infinite h_y_infty h_b_infty)]
                simp [EqSt_0.of.NotInfinite.Infinite h_b_infty h_y_infty]
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
              .
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
                rw [h_st_ab, h_st_xy]
                simp
                rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
                rw [Rat.AddDivS.eq.DivAdd]
                simp [Div.eq.One.of.Ne_0 (Hyperreal.Ne_0.of.NotInfinitesimal h)]
              .
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
                apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
              .
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
                apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
          else if h_b_infty : b → ∞ then
            rw [h_eq']
            have h_by_finite : ¬(b / (b + y)) → ∞ := by
              rw [Rat.Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
              rw [DivAdd.eq.AddDivS]
              rw [Rat.Div.eq.One.of.Ne_0 (by grind)]
              apply Hyperreal.NotInfinite.of.NeSt_0
              rw [Div1.eq.Inv]
              rw [Hyperreal.StInv.eq.InvSt]
              apply Rat.NeInv_0.of.Ne_0
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [Hyperreal.StAdd.eq.Add_St.of.NotInfinite _ (Hyperreal.NotInfiniteDiv.of.NotInfinite.Infinite h_b_infty h_y_infty)]
              simp [EqSt_0.of.NotInfinite.Infinite h_y_infty h_b_infty]
            have h_yb_finite : ¬(y / (b + y)) → ∞ := by
              apply Hyperreal.NotInfiniteDiv.of.NotInfinite.Infinite _ h_y_infty
              rw [Add.comm]
              apply Hyperreal.InfiniteAdd.of.Infinite.NotInfinite h_y_infty h_b_infty
            rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
            .
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
              rw [h_st_ab, h_st_xy]
              simp
              rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
              rw [Rat.AddDivS.eq.DivAdd]
              simp [Div.eq.One.of.Ne_0 (Hyperreal.Ne_0.of.NotInfinitesimal h)]
            .
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
              apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
            .
              apply Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
              apply Hyperreal.NotInfinite.of.NeSt_0 (by grind)
          else
            rw [h_eq]
            have h_a_finite : ¬(a / b * b) → ∞ := by
              rw [EqMulDiv.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
              apply Hyperreal.NotInfinite.of.NotInfinite.XEq h₀ h_b_infty
            have h_x_finite : ¬(x / y * y) → ∞ := by
              rw [EqMulDiv.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
              apply Hyperreal.NotInfinite.of.NotInfinite.XEq h₁ h_y_infty
            rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal _ h]
            .
              apply Rat.EqDiv.of.Eq_Mul.Ne_0
              .
                apply Hyperreal.NeSt_0.of.NotInfinite.NotInfinitesimal
                have := NotInfiniteAdd.of.NotInfinite.NotInfinite h_b_infty h_y_infty
                grind
              .
                simp
                rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_a_finite h_x_finite]
                rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_b_infty h_y_infty]
                repeat rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (Hyperreal.NotInfinite.of.NeSt_0 (by grind)) (by assumption)]
                simp [h_st_ab, h_st_xy]
            .
              apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_a_finite h_x_finite


-- created on 2026-07-25

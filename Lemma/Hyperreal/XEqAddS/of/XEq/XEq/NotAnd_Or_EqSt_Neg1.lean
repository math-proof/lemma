import Lemma.Hyperreal.InfiniteDiv.of.NotInfinitesimal.Infinitesimal
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.EqSt_0.of.NotInfinite.Infinite
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfiniteSub.of.NotInfinite
import Lemma.Hyperreal.Infinitesimal.of.EqSt_0.NotInfinite
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.Infinite
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StAdd.eq.Add_St.of.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.St.of.XEq
import Lemma.Hyperreal.XEq.is.OrAndS
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.EqStDiv.is.InfiniteDiv_Add.of.Ne_Neg.Infinite
import Lemma.Nat.Add
import Lemma.Nat.EqAdd0
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivMul.eq.Mul_Div
import Lemma.Rat.EqMulDiv.of.Ne_0
import Lemma.Rat.Eq.is.EqInv
import Lemma.Int.Eq_Neg.of.Add.eq.Zero
open Hyperreal Nat Rat Int
set_option maxHeartbeats 1000000


@[main]
private lemma main
  {a b x y : ℝ*}
-- given
  (h_or : ¬((b → ∞) ∧ (b + y = 0 ∨ stdPart (b / y) = -1)))
  (h₀ : a ≈ b)
  (h₁ : x ≈ y) :
-- imply
  a + x ≈ b + y := by
-- proof
  have h_or : ¬((b → ∞) ∧ y → ∞ ∧ (b + y = 0 ∨ ((b / (b + y)) → ∞) ∨ (y / (b + y)) → ∞)) := by
    contrapose! h_or
    constructor
    .
      aesop
    .
      obtain ⟨h_b, h_y, h_by | h_div_by | h_div_yb⟩  := h_or
      .
        grind
      .
        if h_by : b + y = 0 then
          left
          assumption
        else
          simp [h_by]
          apply EqStDiv.of.InfiniteDiv_Add.Ne_Neg.Infinite.left h_b (by grind) h_div_by
      .
        if h_by : b + y = 0 then
          left
          assumption
        else
          simp [h_by]
          apply EqStDiv.of.InfiniteDiv_Add.Ne_Neg.Infinite h_y (by grind) h_div_yb
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
          rw [Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
          rw [DivAdd.eq.AddDivS]
          conv =>
            pattern (b + y) / y
            rw [DivAdd.eq.AddDivS]
          rw [Div.eq.One.of.Ne_0 (by grind)]
          have hay := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal ha hy
          have hby := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal hb hy
          have h_st_ay := EqSt_0.of.Infinitesimal hay
          have h_st_xy := EqSt.of.InfinitesimalSub hxy
          have h_st_by := EqSt_0.of.Infinitesimal hby
          have h_eq : stdPart ((a / y + x / y) / (b / y + 1)) = (stdPart (a / y) + stdPart (x / y)) / (stdPart (b / y) + 1) := by
            rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal]
            ·
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite (NotInfinite.of.Infinitesimal hay) (NotInfinite.of.NeSt_0 (by grind))]
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.AddSt.of.NotInfinite (NotInfinite.of.Infinitesimal hby)]
            ·
              apply NotInfinite.of.NeSt_0
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite (NotInfinite.of.Infinitesimal hay) (NotInfinite.of.NeSt_0 (by grind))]
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
          rw [Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
          rw [DivAdd.eq.AddDivS]
          conv =>
            pattern (b + y) / b
            rw [DivAdd.eq.AddDivS]
          rw [Div.eq.One.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
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
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by simp [h_st_ab])) (NotInfinite.of.Infinitesimal hax)]
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
        ·
          exact NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal.comm hb hy
    ·
      have h_st_ab := EqSt.of.InfinitesimalSub hab
      have h_st_xy := EqSt.of.InfinitesimalSub hxy
      have hb0 := Ne_0.of.NotInfinitesimal hb
      have hy0 := Ne_0.of.NotInfinitesimal hy
      if h : (b + y) → 0 then
        simp [h]
        have h_eq : a + x = a / b * b + x / y * y := by
          rw [EqMulDiv.of.Ne_0 hy0]
          rw [EqMulDiv.of.Ne_0 hb0]
        if h_y_infty : y → ∞ then
          if h_b_infty : b → ∞ then
            have h_by_finite : ¬(b / (b + y)) → ∞ := by
              grind
            have : NeZero (b + y) := ⟨by grind⟩
            have := Hyperreal.InfiniteDiv.of.NotInfinitesimal.Infinitesimal hb h
            contradiction
          else
            have h_by_infty := Hyperreal.InfiniteAdd.of.Infinite.NotInfinite h_b_infty h_y_infty
            have := Hyperreal.NotInfinitesimal.of.Infinite h_by_infty
            contradiction
        else if h_b_infty : b → ∞ then
          have h_by_infty := Hyperreal.InfiniteAdd.of.Infinite.NotInfinite h_y_infty h_b_infty
          rw [Add.comm] at h_by_infty
          have := Hyperreal.NotInfinitesimal.of.Infinite h_by_infty
          contradiction
        else
          rw [h_eq]
          apply Infinitesimal.of.EqSt_0.NotInfinite
          ·
            rw [show a / b * b + x / y * y = a / b * (b + y) + (x / y - a / b) * y by grind]
            apply NotInfiniteAdd.of.NotInfinite.NotInfinite
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite
              ·
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_b_infty h_y_infty
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_y_infty
              apply NotInfiniteSub.of.NotInfinite.NotInfinite
              ·
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfinite.of.NeSt_0 (by grind)
          ·
            rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
            ·
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_b_infty]
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_y_infty]
              rw [h_st_ab, h_st_xy]
              simp
              rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_b_infty h_y_infty]
              apply EqSt_0.of.Infinitesimal h
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_b_infty
              apply NotInfinite.of.NeSt_0 (by grind)
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_y_infty
              apply NotInfinite.of.NeSt_0 (by grind)
      else
        simp [h]
        apply InfinitesimalSub.of.EqSt.NotInfinite
        ·
          if h_y_infty : y → ∞ then
            if h_b_infty : b → ∞ then
              have h_x_infty : x → ∞ := by
                apply Infinite.of.NeSt_0.Infinite _ h_y_infty
                grind
              have h_a_infty : a → ∞ := by
                apply Infinite.of.NeSt_0.Infinite _ h_b_infty
                grind
              have h_eq' : (a + x) / (b + y) = a / b * (b / (b + y)) + x / y * (y / (b + y)) := by
                repeat rw [Mul_Div.eq.DivMul]
                repeat rw [EqMulDiv.of.Ne_0 (by grind)]
                rw [AddDivS.eq.DivAdd]
              rw [h_eq']
              have h_by_finite : ¬(b / (b + y)) → ∞ := by
                grind
              have h_yb_finite : ¬(y / (b + y)) → ∞ := by
                grind
              apply NotInfiniteAdd.of.NotInfinite.NotInfinite
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
                apply NotInfinite.of.NeSt_0 (by grind)
            else
              have h_x_infty : x → ∞ := by
                apply Infinite.of.NeSt_0.Infinite _ h_y_infty
                grind
              have h_a_infty : ¬a → ∞ := by
                apply NotInfinite.of.NotInfinite.NeSt_0 h_b_infty
                rw [StDiv.eq.InvStInv]
                grind
              rw [show (a + x) / (b + y) = (a / y + x / y) / (1 + b / y) by grind]
              apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal
              ·
                rw [Add.comm]
                apply NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal (by simp)
                apply InfinitesimalDiv.of.NotInfinite.Infinite h_b_infty h_y_infty
              ·
                rw [Add.comm]
                apply NotInfiniteAdd.of.NotInfinite.NotInfinite
                ·
                  apply NotInfinite.of.NeSt_0 (by grind)
                ·
                  apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal hy h_a_infty
          else if h_b_infty : b → ∞ then
            have h_x_infty : ¬x → ∞ := by
              apply NotInfinite.of.NotInfinite.NeSt_0 h_y_infty
              rw [StDiv.eq.InvStInv]
              grind
            have h_a_infty : a → ∞ := by
              apply Infinite.of.NeSt_0.Infinite _ h_b_infty
              grind
            rw [show (a + x) / (b + y) = (a / b + x / b) / (1 + y / b) by grind]
            apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal
            ·
              rw [Add.comm]
              apply NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal (by simp)
              apply InfinitesimalDiv.of.NotInfinite.Infinite h_y_infty h_b_infty
            ·
              apply NotInfiniteAdd.of.NotInfinite.NotInfinite
              ·
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal hb h_x_infty
          else
            apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h
            apply NotInfiniteAdd.of.NotInfinite.NotInfinite
            ·
              apply NotInfinite.of.NotInfinite.NeSt_0 h_b_infty
              rw [StDiv.eq.InvStInv]
              grind
            ·
              apply NotInfinite.of.NotInfinite.NeSt_0 h_y_infty
              rw [StDiv.eq.InvStInv]
              grind
        ·
          have h_eq : (a + x) / (b + y) = (a / b * b + x / y * y) / (b + y) := by
            rw [EqMulDiv.of.Ne_0 hy0]
            rw [EqMulDiv.of.Ne_0 hb0]
          have h_eq' : (a + x) / (b + y) = a / b * (b / (b + y)) + x / y * (y / (b + y)) := by
            rw [h_eq]
            ring
          if h_y_infty : y → ∞ then
            rw [h_eq']
            if h_b_infty : b → ∞ then
              have h_by_finite : ¬(b / (b + y)) → ∞ := by
                grind
              have h_yb_finite : ¬(y / (b + y)) → ∞ := by
                grind
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
              ·
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
                rw [h_st_ab, h_st_xy]
                simp
                rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
                rw [AddDivS.eq.DivAdd]
                simp [Div.eq.One.of.Ne_0 (Ne_0.of.NotInfinitesimal h)]
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
                apply NotInfinite.of.NeSt_0 (by grind)
            else
              have h_by_finite : ¬(b / (b + y)) → ∞ := by
                apply NotInfiniteDiv.of.NotInfinite.Infinite _ h_b_infty
                apply InfiniteAdd.of.Infinite.NotInfinite h_b_infty h_y_infty
              have h_yb_finite : ¬(y / (b + y)) → ∞ := by
                rw [Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
                rw [DivAdd.eq.AddDivS]
                rw [Div.eq.One.of.Ne_0 (by grind)]
                apply NotInfinite.of.NeSt_0
                rw [Div1.eq.Inv]
                rw [StInv.eq.InvSt]
                apply NeInv_0.of.Ne_0
                rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
                rw [StAdd.eq.AddSt.of.NotInfinite (NotInfiniteDiv.of.NotInfinite.Infinite h_y_infty h_b_infty)]
                simp [EqSt_0.of.NotInfinite.Infinite h_b_infty h_y_infty]
              rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
              ·
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
                rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
                rw [h_st_ab, h_st_xy]
                simp
                rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
                rw [AddDivS.eq.DivAdd]
                simp [Div.eq.One.of.Ne_0 (Ne_0.of.NotInfinitesimal h)]
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
                apply NotInfinite.of.NeSt_0 (by grind)
              ·
                apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
                apply NotInfinite.of.NeSt_0 (by grind)
          else if h_b_infty : b → ∞ then
            rw [h_eq']
            have h_by_finite : ¬(b / (b + y)) → ∞ := by
              rw [Div.eq.DivDivS.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
              rw [DivAdd.eq.AddDivS]
              rw [Div.eq.One.of.Ne_0 (by grind)]
              apply NotInfinite.of.NeSt_0
              rw [Div1.eq.Inv]
              rw [StInv.eq.InvSt]
              apply NeInv_0.of.Ne_0
              rw [show (1 : ℝ*) = (1 : ℝ) by rfl]
              rw [StAdd.eq.Add_St.of.NotInfinite _ (NotInfiniteDiv.of.NotInfinite.Infinite h_b_infty h_y_infty)]
              simp [EqSt_0.of.NotInfinite.Infinite h_y_infty h_b_infty]
            have h_yb_finite : ¬(y / (b + y)) → ∞ := by
              apply NotInfiniteDiv.of.NotInfinite.Infinite _ h_y_infty
              rw [Add.comm]
              apply InfiniteAdd.of.Infinite.NotInfinite h_y_infty h_b_infty
            rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
            ·
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_by_finite]
              rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) h_yb_finite]
              rw [h_st_ab, h_st_xy]
              simp
              rw [AddStS.eq.StAdd.of.NotInfinite.NotInfinite h_by_finite h_yb_finite]
              rw [AddDivS.eq.DivAdd]
              simp [Div.eq.One.of.Ne_0 (Ne_0.of.NotInfinitesimal h)]
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_by_finite
              apply NotInfinite.of.NeSt_0 (by grind)
            ·
              apply NotInfiniteMul.of.NotInfinite.NotInfinite _ h_yb_finite
              apply NotInfinite.of.NeSt_0 (by grind)
          else
            rw [h_eq]
            have h_a_finite : ¬(a / b * b) → ∞ := by
              rw [EqMulDiv.of.Ne_0 (Ne_0.of.NotInfinitesimal hb)]
              apply NotInfinite.of.NotInfinite.XEq h₀ h_b_infty
            have h_x_finite : ¬(x / y * y) → ∞ := by
              rw [EqMulDiv.of.Ne_0 (Ne_0.of.NotInfinitesimal hy)]
              apply NotInfinite.of.NotInfinite.XEq h₁ h_y_infty
            rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal _ h]
            ·
              apply EqDiv.of.Eq_Mul.Ne_0
              ·
                apply NeSt_0.of.NotInfinite.NotInfinitesimal
                have := NotInfiniteAdd.of.NotInfinite.NotInfinite h_b_infty h_y_infty
                grind
              ·
                simp
                rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_a_finite h_x_finite]
                rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_b_infty h_y_infty]
                repeat rw [StMul.eq.MulStS.of.NotInfinite.NotInfinite (NotInfinite.of.NeSt_0 (by grind)) (by assumption)]
                simp [h_st_ab, h_st_xy]
            ·
              apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_a_finite h_x_finite


-- created on 2026-07-25
-- updated on 2026-07-26

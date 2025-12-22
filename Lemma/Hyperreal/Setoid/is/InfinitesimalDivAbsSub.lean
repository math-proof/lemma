import Lemma.Rat.Div.ne.Zero.of.Ne_0.Ne_0
import Lemma.Hyperreal.GeSt.of.Ge.NotInfinite
import Lemma.Hyperreal.Lt0Mul.of.InfinitesimalDivAbsSub.Infinite.Infinite
import Lemma.Rat.DivAbsSub.eq.DivAbsSubDiv.Ne_0.Ne_0
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Eq_0.of.Infinitesimal
import Lemma.Hyperreal.GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAbs
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePow
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.InfiniteMul.of.Infinite.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalAbs
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.Ne_0
import Lemma.Hyperreal.Lt0Mul.is.InfinitesimalDivSquareSub.Infinite.Infinite
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite
import Lemma.Hyperreal.NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite
import Lemma.Hyperreal.NotInfiniteInv.of.Infinite
import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Ge_0.Gt_0
import Lemma.Hyperreal.NotInfinitesimalDivAbsSub.of.Infinite.NotInfinite
import Lemma.Hyperreal.NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite
import Lemma.Hyperreal.Setoid.is.InfinitesimalDivSquareSub
import Lemma.Hyperreal.StAbs.eq.AbsSt
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StAdd.eq.Add_St.of.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Hyperreal.StInv.eq.InvSt
import Lemma.Hyperreal.StSub.eq.SubSt.of.NotInfinite
import Lemma.Int.AbsSub
import Lemma.Int.EqAbs_0.is.Eq_0
import Lemma.Int.GeAbs_0
import Lemma.Int.GeSquare_0
import Lemma.Int.SquareSub
import Lemma.Nat.Add
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSquareSub.eq.DivSubAddDivS.Ne_0.Ne_0
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.Lt0Div.is.Lt0Mul
import Lemma.Rat.MulDivS.eq.One.of.Ne_0.Ne_0
import Lemma.Real.Eq_1.of.AddInv.eq.Two
open Hyperreal Int Nat Rat Real


/--
the operator `≈` (approximately equal) mimics the behavior of [torch.isclose](https://docs.pytorch.org/docs/stable/generated/torch.isclose.html) function, wherein:
- absolute tolerance
  - is defined as `|a - b|`
  - is considered to be `0` in this context, as we are working with hyper-real numbers (with infinites and infinitesimals)
  - if the absolute tolerance `|a - b|` is infinitesimal, then `a` and `b` are guaranteed to be approximately equal, but not vice versa! (e.g., `a` and `b` are both infinite and differ by an infinite quantity, but their relative tolerance could still be infinitesimal)
- relative tolerance
  - is defined as `|a - b| / (|a| + |b| + 1)`
  - the addition of `1` in the denominator ensures stability when both `a` and `b` are close to zero
  - two hyper-real numbers `a` and `b` are considered approximately equal (close to each other) iff this relative tolerance is infinitesimal

| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Setoid.is.InfinitesimalDivAbsSub |
| comm | Hyperreal.InfinitesimalDivAbs.is.Setoid |
| mp | Hyperreal.InfinitesimalDivAbs.of.Setoid |
| mpr | Hyperreal.Setoid.of.InfinitesimalDivAbs |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal (|a - b| / (|a| + |b| + 1)) := by
-- proof
  rw [Setoid.is.InfinitesimalDivSquareSub]
  have h_a_abs := GeAbs_0 a
  have h_b_abs := GeAbs_0 b
  have h_a_square := GeSquare_0 a
  have h_b_square := GeSquare_0 b
  constructor <;>
    intro h
  ·
    if h_inf_a : a.Infinite then
      have h_inf_a_abs := InfiniteAbs.of.Infinite h_inf_a
      if h_inf_b : b.Infinite then
        have h_a_ne_0 := Ne_0.of.Infinite h_inf_a
        have h_b_ne_0 := Ne_0.of.Infinite h_inf_b
        have h_inf_ab := NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite h_inf_a h_inf_b h
        rw [SquareSub.comm] at h
        rw [Add.comm (a := a²)] at h
        have h_inf_ba := NotInfiniteDiv.of.InfinitesimalDivSquareSub.Infinite.Infinite h_inf_b h_inf_a h
        have h_mul_pos := Lt0Mul.is.InfinitesimalDivSquareSub.Infinite.Infinite h_inf_b h_inf_a h
        rw [DivSquareSub.eq.DivSubAddDivS.Ne_0.Ne_0 h_b_ne_0 h_a_ne_0] at h
        have h_inf_add_divs := NotInfiniteAdd.of.NotInfinite.NotInfinite h_inf_ab h_inf_ba
        have h_st_sub_add_divs : st (a / b + b / a - 2) = st (a / b + b / a) - 2 := by
          suffices st (a / b + b / a - (2 : ℝ)) = st (a / b + b / a) - 2 by
            assumption
          rw [StSub.eq.SubSt.of.NotInfinite h_inf_add_divs]
        have h_st_add_add_divs : st (a / b + b / a + 1 / (b * a)) = st (a / b + b / a) := by
          rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_inf_add_divs]
          ·
            simp
            apply EqSt_0.of.Infinitesimal
            apply InfinitesimalMul.of.Infinitesimal.Infinitesimal
            repeat apply InfinitesimalInv.of.Infinite (by assumption)
          ·
            simp
            apply NotInfiniteMul.of.NotInfinite.NotInfinite
            repeat apply NotInfiniteInv.of.Infinite (by assumption)
        have h := EqSt_0.of.Infinitesimal h
        have h_st_div : (b / a).st > 0 := by
          apply GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal _ h_inf_ba
          ·
            apply Lt0Div.of.Lt0Mul h_mul_pos
          ·
            by_contra h_eps_ba
            have := InfinitesimalMul.of.Infinitesimal.NotInfinite h_eps_ba h_inf_ab
            rw [MulDivS.eq.One.of.Ne_0.Ne_0 (by assumption) (by assumption)] at this
            have := NotInfinitesimal.of.Ne_0 (r := 1) (by simp)
            contradiction
        have h_st_add_divs : (a / b + b / a).st ≠ 0 := by
          rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_inf_ab h_inf_ba]
          rw [StDiv.eq.InvStInv (a := a)]
          linarith [GtInv_0.of.Gt_0 h_st_div]
        rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal] at h
        ·
          rw [h_st_sub_add_divs, h_st_add_add_divs] at h
          rw [DivSub.eq.SubDivS] at h
          rw [Div.eq.One.of.Ne_0 h_st_add_divs] at h
          have h := Eq.of.Sub.eq.Zero h
          have h := EqMul.of.Eq_Div.Ne_0 h_st_add_divs h
          simp at h
          rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_inf_ab h_inf_ba] at h
          rw [StDiv.eq.InvStInv (a := a)] at h
          have h_st := Eq_1.of.AddInv.eq.Two h
          have h := InfinitesimalSub.of.EqSt.Ne_0 (by simp) h_st
          have h_a_ne_0 := NeAbs_0.of.Ne_0 h_a_ne_0
          rw [Div.eq.DivDivS.of.Ne_0 h_a_ne_0]
          rw [DivAbsS.eq.AbsDiv]
          rw [DivSub.eq.SubDivS]
          repeat rw [DivAdd.eq.AddDivS]
          repeat rw [Div.eq.One.of.Ne_0 (by assumption)]
          rw [DivAbsS.eq.AbsDiv]
          apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
          ·
            apply InfinitesimalAbs.of.Infinitesimal
            rwa [InfinitesimalSub.comm]
          ·
            apply NotInfinitesimal.of.NeSt_0
            suffices (1 + |b / a| + 1 / |a|).st = 2 by
              linarith
            rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
            ·
              have h_st_inv : |a|⁻¹.st = 0 := by
                simp [StInv.eq.InvSt]
                apply EqSt_0.of.Infinite h_inf_a_abs
              simp [h_st_inv]
              have h_inf_div := NotInfiniteAbs.of.NotInfinite h_inf_ba
              have := StAdd.eq.Add_St.of.NotInfinite h_inf_div (r := 1)
              simp at this
              rw [this]
              rw [StAbs.eq.AbsSt]
              norm_num [h_st]
            ·
              apply NotInfiniteAdd.of.NotInfinite.left
              apply NotInfiniteAbs.of.NotInfinite
              apply NotInfinite.of.NeSt_0
              linarith
            ·
              simp
              apply NotInfiniteInv.of.Infinite h_inf_a_abs
        ·
          apply NotInfiniteSub.of.NotInfinite
          apply NotInfiniteAdd.of.NotInfinite.NotInfinite h_inf_ab h_inf_ba
        ·
          rw [Add.comm]
          apply NotInfinitesimalAdd.of.NotInfinitesimal.Infinitesimal
          ·
            apply NotInfinitesimal.of.NeSt_0 h_st_add_divs
          ·
            apply InfinitesimalDiv.of.NotInfinite.Infinite
            ·
              apply NotInfinite
            ·
              apply InfiniteMul.of.Infinite.Infinite
              repeat assumption
      else
        have := NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite h_inf_a h_inf_b
        contradiction
    else if h_inf_b : b.Infinite then
      have h := NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite h_inf_b h_inf_a
      rw [SquareSub.comm] at h
      rw [Add.comm (a := b²)] at h
      contradiction
    else
      have : NeZero (a² + b² + 1) := ⟨by nlinarith⟩
      have h_inf_add_squares : ¬(a² + b² + 1).Infinite := by
        apply NotInfiniteAdd.of.NotInfinite
        apply NotInfiniteAdd.of.NotInfinite.NotInfinite
        repeat apply NotInfinitePow.of.NotInfinite (by assumption)
      have h := Infinitesimal.of.InfinitesimalDiv.NotInfinite h_inf_add_squares h
      have h := Infinitesimal.of.InfinitesimalPow h
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
      ·
        apply InfinitesimalAbs.of.Infinitesimal h
      ·
        apply NotInfinitesimalAdd.of.Ge_0.Gt_0
        repeat linarith
  ·
    if h_inf_a : a.Infinite then
      have h_inf_a_abs := InfiniteAbs.of.Infinite h_inf_a
      if h_inf_b : b.Infinite then
        have h_a_ne_0 := Ne_0.of.Infinite h_inf_a
        have h_b_ne_0 := Ne_0.of.Infinite h_inf_b
        have h_inf_ab := NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite h_inf_a h_inf_b h
        rw [AbsSub.comm] at h
        rw [Add.comm (a := |a|)] at h
        have h_inf_ba := NotInfiniteDiv.of.InfinitesimalDivAbsSub.Infinite.Infinite h_inf_b h_inf_a h
        have h_mul_pos := Lt0Mul.of.InfinitesimalDivAbsSub.Infinite.Infinite h_inf_b h_inf_a h
        rw [Rat.DivAbsSub.eq.DivAbsSubDiv.Ne_0.Ne_0 h_a_ne_0] at h
        have h_st_sub_add_divs : st |b / a - 1| = |st (b / a) - 1| := by
          rw [StAbs.eq.AbsSt]
          rw [show (1 : ℝ*) = (1 : ℝ) by simp]
          rw [StSub.eq.SubSt.of.NotInfinite h_inf_ba]
        have h_st_add_add_divs : st (|b / a| + |a|⁻¹ + 1) = |st (b / a)| + 1 := by
          rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
          ·
            have h_r := EqSt 1
            simp at h_r
            simp [h_r]
            rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite]
            .
              simp [StAbs.eq.AbsSt]
              apply EqSt_0.of.Infinitesimal
              apply InfinitesimalInv.of.Infinite h_inf_a_abs
            .
              apply NotInfiniteAbs.of.NotInfinite h_inf_ba
            .
              apply NotInfiniteInv.of.Infinite h_inf_a_abs
          ·
            apply NotInfiniteAdd.of.NotInfinite.NotInfinite
            .
              apply NotInfiniteAbs.of.NotInfinite h_inf_ba
            .
              apply NotInfiniteInv.of.Infinite h_inf_a_abs
          .
            apply NotInfinite
        have h := EqSt_0.of.Infinitesimal h
        rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal] at h
        ·
          rw [h_st_sub_add_divs, h_st_add_add_divs] at h
          have h_st_add_divs : |(b / a).st| + 1 ≠ 0 := by
            apply Ne.of.Gt
            apply Lt0Add.of.Gt_0.Gt_0
            .
              apply GtAbs_0.of.Gt_0
              apply GtSt_0.of.Gt_0.NotInfinite.NotInfinitesimal _ h_inf_ba
              ·
                apply Lt0Div.of.Lt0Mul h_mul_pos
              ·
                by_contra h_eps_ba
                have := InfinitesimalMul.of.Infinitesimal.NotInfinite h_eps_ba h_inf_ab
                rw [MulDivS.eq.One.of.Ne_0.Ne_0 h_b_ne_0 h_a_ne_0] at this
                have := NotInfinitesimal.of.Ne_0 (r := 1) (by simp)
                contradiction
            .
              simp
          have h := Eq_0.of.Div.eq.Zero.Ne_0 h h_st_add_divs
          have h := Eq_0.of.EqAbs_0 h
          have h := Eq.of.Sub.eq.Zero h
          have h_a₂_ne_0 := NeSquare_0.of.Ne_0 h_a_ne_0
          rw [Div.eq.DivDivS.of.Ne_0 h_a₂_ne_0]
          rw [AddAdd.eq.Add_Add]
          repeat rw [DivAdd.eq.AddDivS]
          repeat rw [DivSquareS.eq.SquareDiv]
          rw [DivSub.eq.SubDivS]
          repeat rw [Div.eq.One.of.Ne_0 (by assumption)]
          simp
          apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
          ·
            apply InfinitesimalSquare.of.Infinitesimal
            rw [InfinitesimalSub.comm]
            apply InfinitesimalSub.of.EqSt.NotInfinite h_inf_ba h
          ·
            rw [Add.comm]
            apply NotInfinitesimalAdd.of.Ge_0.Gt_0
            .
              apply Le0Add.of.Ge_0.Ge_0
              .
                apply GeSquare_0
              .
                simp
                apply GeSquare_0
            .
              simp
        ·
          apply NotInfiniteAbs.of.NotInfinite
          apply NotInfiniteSub.of.NotInfinite h_inf_ba
        ·
          apply NotInfinitesimalAdd.of.Ge_0.Gt_0
          ·
            apply Le0Add.of.Ge_0.Ge_0
            .
              apply GeAbs_0
            .
              simp
          ·
            simp
        else
          have := NotInfinitesimalDivAbsSub.of.Infinite.NotInfinite h_inf_a h_inf_b
          contradiction
    else if h_inf_b : b.Infinite then
      have h := NotInfinitesimalDivAbsSub.of.Infinite.NotInfinite h_inf_b h_inf_a
      rw [AbsSub.comm] at h
      rw [Add.comm (a := |b|)] at h
      contradiction
    else
      have : NeZero (|a| + |b| + 1) := ⟨by linarith⟩
      have h_inf_add_abss : ¬(|a| + |b| + 1).Infinite := by
        apply NotInfiniteAdd.of.NotInfinite
        apply NotInfiniteAdd.of.NotInfinite.NotInfinite
        repeat apply NotInfiniteAbs.of.NotInfinite (by assumption)
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
      .
        apply InfinitesimalSquare.of.Infinitesimal
        apply Infinitesimal.of.InfinitesimalAbs
        apply Infinitesimal.of.InfinitesimalDiv.NotInfinite h_inf_add_abss h
      .
        have h_inf_add_squares : ¬(a² + b² + 1).Infinite := by
          apply NotInfiniteAdd.of.NotInfinite
          apply NotInfiniteAdd.of.NotInfinite.NotInfinite
          repeat apply NotInfiniteSquare.of.NotInfinite (by assumption)
        have h_ge_add_add_square : (a² + b² + 1) ≥ 1 := by nlinarith
        have := Hyperreal.GeSt.of.Ge.NotInfinite h_inf_add_squares h_ge_add_add_square
        apply NotInfinitesimal.of.NeSt_0
        linarith


-- created on 2025-12-09
-- updated on 2025-12-21

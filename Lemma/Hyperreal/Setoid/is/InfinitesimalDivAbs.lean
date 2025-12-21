import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Eq_0.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAbs
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePow
import Lemma.Hyperreal.Infinite.is.InfiniteSquare
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalAbs
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Ge_0.Gt_0
import Lemma.Hyperreal.Setoid.is.InfinitesimalDivSquareSub
import Lemma.Hyperreal.StAbs.eq.AbsSt
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StPow.eq.PowSt.of.NotInfinite
import Lemma.Int.EqAbs_0.is.Eq_0
import Lemma.Int.GeAbs_0
import Lemma.Int.GeSquare_0
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Eq_0.is.EqSquare_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.SquareDiv.eq.DivSquareS
open Hyperreal Int Nat Rat


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
    apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
    ·
      if h_inf_a : a.Infinite then
        if h_inf_b : b.Infinite then
          sorry
        else
          have h_a_ne_0 := Ne_0.of.Infinite h_inf_a
          have h_a₂_ne_0 := NeSquare_0.of.Ne_0 h_a_ne_0
          rw [Div.eq.DivDivS.of.Ne_0 h_a₂_ne_0] at h
          rw [DivSquareS.eq.SquareDiv] at h
          rw [AddAdd.eq.Add_Add] at h
          rw [DivAdd.eq.AddDivS] at h
          rw [DivSub.eq.SubDivS] at h
          repeat rw [Div.eq.One.of.Ne_0 (by assumption)] at h
          have h_inf_div_ba := InfinitesimalDiv.of.NotInfinite.Infinite h_inf_b h_inf_a
          have h_fin_sub_div : ¬(1 - b / a).Infinite := by
            apply NotInfiniteSub.of.NotInfinite.left
            apply NotInfinite.of.Infinitesimal h_inf_div_ba
          have h_fin_square := NotInfiniteSquare.of.NotInfinite h_fin_sub_div
          have h_eps_add_div_square : ¬(1 + (b ^ 2 + 1) / a ^ 2).Infinitesimal := by
            apply NotInfinitesimalAdd.of.Ne_0.Infinitesimal.left
            apply InfinitesimalDiv.of.NotInfinite.Infinite
            ·
              apply NotInfiniteAdd.of.NotInfinite
              apply NotInfinitePow.of.NotInfinite h_inf_b
            ·
              apply InfinitePow.of.Infinite h_inf_a
            ·
              simp
          have h_st_square_sub : st (1 - b / a)² = 1 := by
            rw [StPow.eq.PowSt.of.NotInfinite h_fin_sub_div]
            suffices st (1 - b / a) = 1 by
              simp [this]
            apply EqSt.of.InfinitesimalSub
            simpa
          have h_st_add_div_square : st (1 + (b² + 1) / a²) = 1 := by
            apply EqSt.of.InfinitesimalSub
            simp
            apply InfinitesimalDiv.of.NotInfinite.Infinite
            ·
              apply NotInfiniteAdd.of.NotInfinite
              apply NotInfinitePow.of.NotInfinite h_inf_b
            ·
              apply InfinitePow.of.Infinite h_inf_a
          have h_st_div := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_fin_square h_eps_add_div_square
          simp [h_st_square_sub, h_st_add_div_square] at h_st_div
          have h := NotInfinitesimal.of.NeSt_0 (by linarith)
          contradiction
      else if h_inf_b : b.Infinite then
        sorry
      else
        have : NeZero (a ^ 2 + b ^ 2 + 1) := ⟨by nlinarith⟩
        have h_inf_add_squares : ¬(a ^ 2 + b ^ 2 + 1).Infinite := by
          apply NotInfiniteAdd.of.NotInfinite
          apply NotInfiniteAdd.of.NotInfinite.NotInfinite
          repeat apply NotInfinitePow.of.NotInfinite (by assumption)
        have := Infinitesimal.of.InfinitesimalDiv.NotInfinite h_inf_add_squares h
        have := Infinitesimal.of.InfinitesimalPow this
        apply InfinitesimalAbs.of.Infinitesimal this
    ·
      apply NotInfinitesimalAdd.of.Ge_0.Gt_0
      repeat linarith
  ·
    apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
    ·
      if h_inf_a : a.Infinite then
        if h_inf_b : b.Infinite then
          sorry
        else
          have h_a_ne_0 := Ne_0.of.Infinite h_inf_a
          have h_a_abs_ne_0 := NeAbs_0.of.Ne_0 h_a_ne_0
          rw [Div.eq.DivDivS.of.Ne_0 h_a_abs_ne_0] at h
          rw [DivAbsS.eq.AbsDiv] at h
          rw [AddAdd.eq.Add_Add] at h
          rw [DivAdd.eq.AddDivS] at h
          rw [DivSub.eq.SubDivS] at h
          repeat rw [Div.eq.One.of.Ne_0 (by assumption)] at h
          have h_inf_div_ba := InfinitesimalDiv.of.NotInfinite.Infinite h_inf_b h_inf_a
          have h_fin_sub_div : ¬(1 - b / a).Infinite := by
            apply NotInfiniteSub.of.NotInfinite.left
            apply NotInfinite.of.Infinitesimal h_inf_div_ba
          have h_fin_abs := NotInfiniteAbs.of.NotInfinite h_fin_sub_div
          have h_eps_add_div_abs : ¬(1 + (|b| + 1) / |a|).Infinitesimal := by
            apply NotInfinitesimalAdd.of.Ne_0.Infinitesimal.left
            apply InfinitesimalDiv.of.NotInfinite.Infinite
            ·
              apply NotInfiniteAdd.of.NotInfinite
              apply NotInfiniteAbs.of.NotInfinite h_inf_b
            ·
              apply InfiniteAbs.of.Infinite h_inf_a
            ·
              simp
          have h_st_square_sub : st |1 - b / a| = 1 := by
            rw [StAbs.eq.AbsSt]
            suffices st (1 - b / a) = 1 by
              simp [this]
            apply EqSt.of.InfinitesimalSub
            simpa
          have h_st_add_div_abs : st (1 + (|b| + 1) / |a|) = 1 := by
            apply EqSt.of.InfinitesimalSub
            simp
            apply InfinitesimalDiv.of.NotInfinite.Infinite
            ·
              apply NotInfiniteAdd.of.NotInfinite
              apply NotInfiniteAbs.of.NotInfinite h_inf_b
            ·
              apply InfiniteAbs.of.Infinite h_inf_a
          have h_st_div := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_fin_abs h_eps_add_div_abs
          simp [h_st_square_sub, h_st_add_div_abs] at h_st_div
          have h := NotInfinitesimal.of.NeSt_0 (by linarith)
          contradiction
      else if h_inf_b : b.Infinite then
        sorry
      else
        have : NeZero (|a| + |b| + 1) := ⟨by linarith⟩
        have h_inf_add_abss : ¬(|a| + |b| + 1).Infinite := by
          apply NotInfiniteAdd.of.NotInfinite
          apply NotInfiniteAdd.of.NotInfinite.NotInfinite
          repeat apply NotInfiniteAbs.of.NotInfinite (by assumption)
        have := Infinitesimal.of.InfinitesimalDiv.NotInfinite h_inf_add_abss h
        have := Infinitesimal.of.InfinitesimalAbs this
        apply InfinitesimalPow.of.Infinitesimal this
    ·
      apply NotInfinitesimalAdd.of.Ge_0.Gt_0
      repeat linarith


-- created on 2025-12-09
-- updated on 2025-12-21

import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Eq_0.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAbs
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.StAbs.eq.AbsSt
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Int.EqAbs_0.is.Eq_0
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
open Hyperreal Nat Rat Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_inf_a : a.Infinite)
  (h_inf_b : ¬b.Infinite) :
-- imply
  ¬Infinitesimal (|a - b| / (|a| + |b| + 1)) := by
-- proof
  have h_a_ne_0 := Ne_0.of.Infinite h_inf_a
  have h_a_abs_ne_0 := NeAbs_0.of.Ne_0 h_a_ne_0
  rw [Div.eq.DivDivS.of.Ne_0 h_a_abs_ne_0]
  rw [DivAbsS.eq.AbsDiv]
  rw [AddAdd.eq.Add_Add]
  rw [DivAdd.eq.AddDivS]
  rw [DivSub.eq.SubDivS]
  repeat rw [Div.eq.One.of.Ne_0 (by assumption)]
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
  apply NotInfinitesimal.of.NeSt_0 (by linarith)


-- created on 2025-12-21

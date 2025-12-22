import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAbs
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalAbs
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Gt_0.Ge_0
import Lemma.Hyperreal.StAbs.eq.AbsSt
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Int.EqAbs_0.is.Eq_0
import Lemma.Int.GeAbs_0
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Le0Add.of.Ge_0.Ge_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.GeInvAbs_0
open Hyperreal Int Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : Infinite b)
  (h : Infinitesimal (|a - b| / (|a| + |b| + 1))) :
-- imply
  ¬Infinite (a / b) := by
-- proof
  by_contra h_inf_ba
  have h_a_ne_0 := Ne_0.of.Infinite h_a
  have h_b_ne_0 := Ne_0.of.Infinite h_b
  have h_a_abs_ne_0 := NeAbs_0.of.Ne_0 h_a_ne_0
  rw [Div.eq.DivDivS.of.Ne_0 h_a_abs_ne_0] at h
  rw [AddAdd.eq.Add_Add] at h
  repeat rw [DivAdd.eq.AddDivS] at h
  repeat rw [DivAbsS.eq.AbsDiv] at h
  rw [DivSub.eq.SubDivS] at h
  simp [Div.eq.One.of.Ne_0 h_a_ne_0] at h
  have h_eps_ab := InfinitesimalDiv.of.InfiniteDiv h_inf_ba
  have h_st_square_sub_div : st |1 - b / a| = 1 := by
    rw [StAbs.eq.AbsSt]
    suffices (1 - b / a).st = 1 by
      simp [this]
    apply EqSt.of.InfinitesimalSub
    simpa
  have h_st_add_add_square : st (1 + (|b / a| + |a|⁻¹)) = 1 := by
    apply EqSt.of.InfinitesimalSub
    simp
    apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
    ·
      apply InfinitesimalAbs.of.Infinitesimal h_eps_ab
    ·
      apply InfinitesimalInv.of.Infinite
      apply InfiniteAbs.of.Infinite h_a
  have h_inf_abs_sub_div : ¬(|1 - b / a|).Infinite := by
    apply NotInfiniteAbs.of.NotInfinite
    apply NotInfiniteSub.of.NotInfinite.left
    apply NotInfinite.of.Infinitesimal h_eps_ab
  have h_eps_add_add_abs : ¬(1 + (|b / a| + |a|⁻¹)).Infinitesimal := by
    apply NotInfinitesimalAdd.of.Gt_0.Ge_0
    ·
      simp
    ·
      apply Le0Add.of.Ge_0.Ge_0
      ·
        apply GeAbs_0
      ·
        apply GeInvAbs_0
  have h_div := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_inf_abs_sub_div h_eps_add_add_abs
  rw [h_st_square_sub_div, h_st_add_add_square] at h_div
  have := NotInfinitesimal.of.NeSt_0 (by linarith)
  contradiction


-- created on 2025-12-22

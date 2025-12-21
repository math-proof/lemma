import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteSquare
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
import Lemma.Hyperreal.InfinitesimalSquare.of.Infinitesimal
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Gt_0.Ge_0
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StPow.eq.PowSt.of.NotInfinite
import Lemma.Int.GeSquare_0
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.Eq_0.is.EqSquare_0
import Lemma.Nat.Le0Add.of.Ge_0.Ge_0
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.GeInvSquare_0
import Lemma.Rat.SquareDiv.eq.DivSquareS
open Hyperreal Int Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : Infinite b)
  (h : Infinitesimal ((a - b)² / (a² + b² + 1))) :
-- imply
  ¬Infinite (a / b) := by
-- proof
  by_contra h_inf_ba
  have h_a_ne_0 := Ne_0.of.Infinite h_a
  have h_b_ne_0 := Ne_0.of.Infinite h_b
  have h_a₂_ne_0 := NeSquare_0.of.Ne_0 h_a_ne_0
  rw [Div.eq.DivDivS.of.Ne_0 h_a₂_ne_0] at h
  rw [AddAdd.eq.Add_Add] at h
  repeat rw [DivAdd.eq.AddDivS] at h
  repeat rw [DivSquareS.eq.SquareDiv] at h
  rw [DivSub.eq.SubDivS] at h
  simp [Div.eq.One.of.Ne_0 h_a_ne_0] at h
  have h_eps_ab := InfinitesimalDiv.of.InfiniteDiv h_inf_ba
  have h_st_square_sub_div : st (1 - b / a)² = 1 := by
    rw [StPow.eq.PowSt.of.NotInfinite]
    ·
      suffices (1 - b / a).st = 1 by
        simp [this]
      apply EqSt.of.InfinitesimalSub
      simpa
    ·
      apply NotInfiniteSub.of.NotInfinite.left
      apply NotInfinite.of.Infinitesimal h_eps_ab
  have h_st_add_add_square : st (1 + ((b / a)² + (a²)⁻¹)) = 1 := by
    apply EqSt.of.InfinitesimalSub
    simp
    apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
    ·
      apply InfinitesimalSquare.of.Infinitesimal h_eps_ab
    ·
      apply InfinitesimalInv.of.Infinite
      apply InfiniteSquare.of.Infinite h_a
  have h_inf_square_sub_div : ¬((1 - b / a)²).Infinite := by
    apply NotInfiniteSquare.of.NotInfinite
    apply NotInfiniteSub.of.NotInfinite.left
    apply NotInfinite.of.Infinitesimal h_eps_ab
  have h_eps_add_add_square : ¬(1 + ((b / a)² + (a²)⁻¹)).Infinitesimal := by
    apply NotInfinitesimalAdd.of.Gt_0.Ge_0
    ·
      simp
    ·
      apply Le0Add.of.Ge_0.Ge_0
      ·
        apply GeSquare_0
      ·
        apply GeInvSquare_0
  have h_div := StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal h_inf_square_sub_div h_eps_add_add_square
  rw [h_st_square_sub_div, h_st_add_add_square] at h_div
  have := NotInfinitesimal.of.NeSt_0 (by linarith)
  contradiction


-- created on 2025-12-21

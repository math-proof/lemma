import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteSquare
import Lemma.Hyperreal.Infinite.is.InfiniteSub
import Lemma.Hyperreal.Infinite.is.InfiniteSub.of.NotInfinite
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.Infinite
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.Infinite
import Lemma.Hyperreal.InfinitesimalDiv.of.NotInfinite.Infinite
import Lemma.Hyperreal.InfinitesimalSquare.of.Infinitesimal
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.StAdd.eq.AddSt.of.NotInfinite
import Lemma.Hyperreal.StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.StPow.eq.PowSt.of.NotInfinite
import Lemma.Int.Eq_0.is.EqSquare_0
import Lemma.Int.SquareSub
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.SquareDiv.eq.DivSquareS
open Hyperreal Int Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a.Infinitesimal)
  (h : Infinitesimal ((a - b)² / (1 + a² + b²))) :
-- imply
  ¬(1 + a ^ 2 + b ^ 2).Infinite := by
-- proof
  by_contra h'
  rw [AddAdd.eq.Add_Add] at h'
  have h' := Infinite.of.InfiniteAdd.left h'
  have h_a₂ := InfinitesimalSquare.of.Infinitesimal h_a
  have h_a₂ := NotInfinite.of.Infinitesimal h_a₂
  have h_b₂ := InfiniteSub.of.Infinite.NotInfinite h_a₂ h'
  simp at h_b₂
  have h_b₂_ne_0 := Ne_0.of.Infinite h_b₂
  rw [Div.eq.DivDivS.of.Ne_0 h_b₂_ne_0] at h
  rw [DivSquareS.eq.SquareDiv] at h
  rw [DivAdd.eq.AddDivS] at h
  rw [DivSub.eq.SubDivS] at h
  have h_b_ne_0 := Ne_0.of.NeSquare_0 h_b₂_ne_0
  repeat rw [Div.eq.One.of.Ne_0 (by assumption)] at h
  have h_b := Infinite.of.InfiniteSquare h_b₂
  have h := EqSt_0.of.Infinitesimal h
  have h_eq_st_add_div_square : st ((1 + a²) / b² + 1) = 1 := by
    apply EqSt.of.InfinitesimalSub
    simp
    apply InfinitesimalDiv.of.NotInfinite.Infinite _ h_b₂
    apply NotInfiniteAdd.of.NotInfinite.left h_a₂
  rw [StDiv.eq.DivStS.of.NotInfinite.NotInfinitesimal] at h
  ·
    have h_eq_st_square_sub : st (a / b - 1)² = 1 := by
      rw [SquareSub.comm]
      rw [StPow.eq.PowSt.of.NotInfinite]
      ·
        suffices st (1 - a / b) = 1 by
          simp [this]
        apply EqSt.of.InfinitesimalSub
        simp
        apply InfinitesimalDiv.of.Infinitesimal.Infinite h_a h_b
      ·
        apply NotInfiniteSub.of.NotInfinite.left
        apply NotInfiniteDiv.of.NotInfinite.Infinite h_b
        apply NotInfinite.of.Infinitesimal h_a
    simp [h_eq_st_square_sub, h_eq_st_add_div_square] at h
  ·
    apply NotInfiniteSquare.of.NotInfinite
    apply NotInfiniteSub.of.NotInfinite
    apply NotInfiniteDiv.of.NotInfinite.Infinite h_b
    apply NotInfinite.of.Infinitesimal h_a
  ·
    apply NotInfinitesimal.of.NeSt_0
    linarith


-- created on 2025-12-19
-- updated on 2025-12-20

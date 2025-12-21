import Lemma.Hyperreal.Infinite.is.InfiniteAbs
import Lemma.Hyperreal.Infinite.is.InfiniteAdd
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.Infinite.is.InfinitePow
import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalAbs
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Ge_0.Gt_0
import Lemma.Hyperreal.NotInfinitesimalDivAbsSub.of.Infinite.NotInfinite
import Lemma.Hyperreal.NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite
import Lemma.Hyperreal.Setoid.is.InfinitesimalDivSquareSub
import Lemma.Int.AbsSub
import Lemma.Int.GeAbs_0
import Lemma.Int.GeSquare_0
import Lemma.Int.SquareSub
import Lemma.Nat.Add
open Hyperreal Int Nat


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
          have := NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite h_inf_a h_inf_b
          contradiction
      else if h_inf_b : b.Infinite then
        have h := NotInfinitesimalDivSquareSub.of.Infinite.NotInfinite h_inf_b h_inf_a
        rw [SquareSub.comm] at h
        rw [Add.comm (a := b²)] at h
        contradiction
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
        have := Infinitesimal.of.InfinitesimalDiv.NotInfinite h_inf_add_abss h
        have := Infinitesimal.of.InfinitesimalAbs this
        apply InfinitesimalPow.of.Infinitesimal this
    ·
      apply NotInfinitesimalAdd.of.Ge_0.Gt_0
      repeat linarith


-- created on 2025-12-09
-- updated on 2025-12-21

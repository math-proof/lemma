import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.InfinitesimalDivSquareSub
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.NotInfiniteDiv_AddAddSquareS.of.StDiv.eq.One
import Lemma.Hyperreal.Eq_0.of.InfinitesimalAdd.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.StDiv.eq.One.of.InfinitesimalDivSquareSub.NotInfinitesimal.NotInfinitesimal
import Lemma.Hyperreal.StDiv_AddAddSquareS.eq.One.of.StDiv.eq.One
import Lemma.Int.SquareSub
import Lemma.Nat.AddAdd
import Lemma.Rat.DivSquareSub.eq.Sub1DivAddS
open Hyperreal Int Nat Rat


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal ((a - b)² / (a² + b² + 1)) := by
-- proof
  rw [Setoid.is.OrAndS]
  constructor <;>
    intro h
  ·
    obtain h | h := h
    ·
      let ⟨h_a, h_b⟩ := h
      apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
      ·
        apply InfinitesimalPow.of.Infinitesimal
        apply InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a h_b
      ·
        apply NotInfinitesimalAdd.of.Ne_0.Infinitesimal
        ·
          apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
          repeat exact InfinitesimalPow.of.Infinitesimal (by assumption)
        ·
          simp
    ·
      let ⟨h_ab, h_b⟩ := h
      if h_a : a.Infinitesimal then
        have h_ab_div := InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h_a h_b
        have := NotInfinitesimalSub.of.Infinitesimal.Ne_0 h_ab_div (by simp) (r := 1)
        contradiction
      else
        have h := EqSt.of.InfinitesimalSub h_ab
        rw [DivSquareSub.eq.Sub1DivAddS]
        rw [InfinitesimalSub.comm]
        apply InfinitesimalSub.of.EqSt.NotInfinite
        ·
          apply NotInfiniteDiv_AddAddSquareS.of.StDiv.eq.One h
        ·
          apply StDiv_AddAddSquareS.eq.One.of.StDiv.eq.One h
  ·
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        have := Infinitesimal.of.Infinitesimal.InfinitesimalDivSquareSub h h_a
        contradiction
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        rw [SquareSub.comm] at h
        conv at h =>
          arg 1
          arg 2
          arg 1
          rw [Add.comm]
        have := Infinitesimal.of.Infinitesimal.InfinitesimalDivSquareSub h h_b
        contradiction
      else
        simp [h_b]
        rw [DivSquareSub.eq.Sub1DivAddS] at h
        rw [InfinitesimalSub.comm] at h
        have h := EqSt.of.InfinitesimalSub h
        have h := StDiv.eq.One.of.InfinitesimalDivSquareSub.NotInfinitesimal.NotInfinitesimal h_a h_b h
        apply InfinitesimalSub.of.EqSt.NotInfinite _ h
        apply NotInfinite.of.NeSt_0
        linarith


-- created on 2025-12-09
-- updated on 2025-12-20

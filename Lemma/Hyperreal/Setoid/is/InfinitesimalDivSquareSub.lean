import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalPow
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.InfinitesimalDivSquare
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.NotInfiniteDiv_Add_Square.of.StDiv.eq.One
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.StDiv.eq.One.is.InfinitesimalDivSquareSub.of.NotInfinitesimal.NotInfinitesimal
import Lemma.Hyperreal.StDiv_Add_Square.eq.One.of.StDiv.eq.One
import Lemma.Int.SquareSub
import Lemma.Nat.Add
import Lemma.Nat.AddAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Rat.DivSquareSub.eq.Sub1DivAddS
import sympy.sets.fancyset
open Hyperreal Int Nat Rat


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal ((a - b)² / (1 + a² + b²)) := by
-- proof
  rw [Setoid.is.OrAndS]
  constructor
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
        rw [AddAdd.eq.Add_Add]
        rw [Add.comm]
        apply NotInfinitesimalAdd.of.Infinitesimal.Ne_0
        ·
          apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal
          ·
            exact InfinitesimalPow.of.Infinitesimal h_a
          ·
            exact InfinitesimalPow.of.Infinitesimal h_b
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
        apply InfinitesimalDivSquareSub.of.StDiv.eq.One.NotInfinitesimal.NotInfinitesimal h_a h_b h
  ·
    intro h
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        have := Infinitesimal.of.Infinitesimal.InfinitesimalDivSquare h h_a
        contradiction
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        rw [SquareSub.comm] at h
        rw [AddAdd.comm] at h
        have := Infinitesimal.of.Infinitesimal.InfinitesimalDivSquare h h_b
        contradiction
      else
        simp [h_b]
        have h_st_ab := StDiv.eq.One.of.InfinitesimalDivSquareSub.NotInfinitesimal.NotInfinitesimal h_a h_b h
        apply InfinitesimalSub.of.EqSt.NotInfinite _ h_st_ab
        apply NotInfinite.of.NeSt_0
        linarith


-- created on 2025-12-09
-- updated on 2025-12-20

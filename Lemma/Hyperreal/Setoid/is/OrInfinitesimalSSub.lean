import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.NotInfiniteDiv.of.InfinitesimalSubAddDivS.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.of.Infinitesimal.InfinitesimalSub
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSub.Infinitesimal
import Lemma.Hyperreal.Infinitesimal.of.InfinitesimalSubAddDivS.Infinitesimal
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Nat.Add
import Lemma.Rat.SubDiv.eq.DivSub.of.Ne_0
import Lemma.Real.Eq_1.of.Add_Inv.eq.Two
open Hyperreal Nat Rat Real


@[main, comm, mp, mpr]
private lemma main
-- given
  (a b : ℝ*) :
-- imply
  a ≈ b ↔ Infinitesimal (a - b) ∨ Infinitesimal (a / b + b / a - 2) := by
-- proof
  rw [show (2 : ℝ*) = (2 : ℝ) by rfl]
  rw [Setoid.is.OrAndS]
  constructor
  <;> intro h
  <;> obtain h | h := h
  ·
    let ⟨h_a, h_b⟩ := h
    left
    apply InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a h_b
  ·
    let ⟨h_r, h_b⟩ := h
    right
    simp
    rw [show a / b + b / a - 2 = (a / b - 1) + (b / a - 1) by ring]
    apply InfinitesimalAdd.of.Infinitesimal.Infinitesimal h_r
    have h_r := EqSt.of.InfinitesimalSub h_r
    rw [StDiv.eq.InvStInv] at h_r
    simp at h_r
    apply InfinitesimalSub.of.EqSt.NotInfinite _ h_r
    apply NotInfinite.of.NeSt_0
    linarith
  ·
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        have := NotInfinitesimalSub.of.Infinitesimal.NotInfinitesimal h_a h_b
        contradiction
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        have := NotInfinitesimalSub.of.NotInfinitesimal.Infinitesimal h_a h_b
        contradiction
      else
        simp [h_b]
        rw [SubDiv.eq.DivSub.of.Ne_0 (by grind)]
        apply InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal h h_b
  ·
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        have := NotInfinitesimalSubAddDivS.of.NotInfinitesimal.Infinitesimal h_a h_b (d := 2)
        contradiction
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        rw [Add.comm] at h
        have := NotInfinitesimalSubAddDivS.of.NotInfinitesimal.Infinitesimal h_b h_a (d := 2)
        contradiction
      else
        simp [h_b]
        have h_st := EqSt.of.InfinitesimalSub h
        rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite] at h_st
        ·
          conv_lhs at h_st =>
            arg 2
            rw [StDiv.eq.InvStInv]
          have h := Eq_1.of.Add_Inv.eq.Two h_st
          apply InfinitesimalSub.of.EqSt.NotInfinite _ h
          apply NotInfinite.of.NeSt_0
          linarith
        ·
          apply NotInfiniteDiv.of.InfinitesimalSubAddDivS.NotInfinitesimal h_a h
        ·
          rw [Add.comm] at h
          apply NotInfiniteDiv.of.InfinitesimalSubAddDivS.NotInfinitesimal h_b h


-- created on 2025-12-09
-- updated on 2025-12-11

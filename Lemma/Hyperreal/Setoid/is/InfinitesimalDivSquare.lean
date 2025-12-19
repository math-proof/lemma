import Lemma.Hyperreal.Infinite.of.InfinitesimalDiv.NotInfinitesimal
import Lemma.Hyperreal.NotInfiniteDiv_Add_Square.of.StDiv.eq.One
import Lemma.Hyperreal.Gt_0.of.GtSt_0
import Lemma.Rat.Div.gt.Zero.is.Mul.gt.Zero
import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalAdd.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalDiv.of.Infinitesimal.NotInfinitesimal
import Lemma.Hyperreal.InfinitesimalPow.of.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub.is.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.Ne_0.of.Infinitesimal
import Lemma.Hyperreal.NotInfinitesimalAdd.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.NotInfinitesimalSub.of.Infinitesimal.Ne_0
import Lemma.Hyperreal.Setoid.is.OrAndS
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Rat.DivSquareSub.eq.Sub1DivAddS
import Lemma.Rat.Div_AddS1.eq.Add1DivSquareSub.of.Mul.gt.Zero
import sympy.core.power
import sympy.sets.fancyset
open Hyperreal Nat Rat


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
        have h_ab := EqSt.of.InfinitesimalSub h_ab
        have h_ba := StDiv.eq.InvStInv (a := b) (b := a)
        rw [h_ab] at h_ba
        simp at h_ba
        have h_a := Ne_0.of.Infinitesimal h_a
        have h_b := Ne_0.of.Infinitesimal h_b
        rw [DivSquareSub.eq.Sub1DivAddS]
        apply InfinitesimalSub.of.InfinitesimalSub
        apply InfinitesimalSub.of.EqSt.NotInfinite
        ·
          apply NotInfiniteDiv_Add_Square.of.StDiv.eq.One h_ab
        ·
          apply StDiv_Add_Square.eq.One.of.StDiv.eq.One h_ab
  ·
    intro h
    if h_a : a.Infinitesimal then
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
      else
        simp [h_b]
        have : NeZero (1 + a ^ 2 + b ^ 2) := ⟨by
          sorry
        ⟩
        have := Infinitesimal.of.InfinitesimalDiv.NotInfinite (by sorry) h
        -- contradiction
        sorry
    else
      simp [h_a]
      if h_b : b.Infinitesimal then
        simp [h_b]
        -- contradiction
        sorry
      else
        simp [h_b]
        sorry


-- created on 2025-12-09
-- updated on 2025-12-11

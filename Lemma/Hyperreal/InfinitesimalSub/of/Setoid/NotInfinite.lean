import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.Infinite.is.Infinite.of.Setoid
import Lemma.Hyperreal.Infinite.of.InfiniteDiv.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.Infinitesimal.of.Setoid
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.InfinitesimalSub.of.StDiv.eq.One.NotInfinite
import Lemma.Hyperreal.Setoid.is.OrInfinitesimalSSub
import Lemma.Hyperreal.StAdd.eq.AddStS.of.NotInfinite.NotInfinite
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Real.Eq_1.of.Add_Inv.eq.Two
open Hyperreal Real


@[main, mt 1]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a.Infinite)
  (h : a ≈ b) :
-- imply
  (a - b).Infinitesimal := by
-- proof
  have h' := h.symm
  have h_b := NotInfinite.of.NotInfinite.Setoid h' h_a
  obtain h_eps | h_eps := OrInfinitesimalSSub.of.Setoid h
  ·
    assumption
  ·
    if h_a_eps : a.Infinitesimal then
      apply InfinitesimalSub.of.Infinitesimal.Infinitesimal h_a_eps
      apply Infinitesimal.of.Infinitesimal.Setoid h h_a_eps
    else
      have h_b_eps := NotInfinitesimal.of.NotInfinitesimal.Setoid h' h_a_eps
      rw [show (2 : ℝ*) = (2 : ℝ) by rfl] at h_eps
      have h_st := EqSt.of.InfinitesimalSub h_eps
      have h_div_ab := NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h_b_eps h_a
      rw [StAdd.eq.AddStS.of.NotInfinite.NotInfinite h_div_ab] at h_st
      ·
        apply InfinitesimalSub.of.StDiv.eq.One.NotInfinite h_a
        apply Eq_1.of.Add_Inv.eq.Two
        rwa [InvStInv.eq.StDiv]
      ·
        apply NotInfiniteDiv.of.NotInfinite.NotInfinitesimal h_a_eps h_b


-- created on 2025-12-27
-- updated on 2025-12-28

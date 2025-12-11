import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
import Lemma.Hyperreal.InfinitesimalSub.of.Infinitesimal.Infinitesimal
import Lemma.Hyperreal.NotInfinite.of.NeSt_0
import Lemma.Int.AddSub.eq.SubAdd
import Lemma.Int.EqSubAdd
import Lemma.Nat.Ne_0.of.Eq
open Hyperreal Int Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
-- given
  (h_a : ¬Infinitesimal a)
  (h : Infinitesimal (a / b + b / a - d)) :
-- imply
  ¬Infinite (a / b) := by
-- proof
  have h : Infinitesimal (a / b + b / a - (d : ℝ)) := h
  contrapose! h_a
  have h_ba := InfinitesimalDiv.of.InfiniteDiv h_a
  have h_sub := InfinitesimalSub.of.Infinitesimal.Infinitesimal h h_ba
  rw [SubAdd.eq.AddSub] at h_sub
  rw [EqSubAdd] at h_sub
  have h_st := EqSt.of.InfinitesimalSub h_sub
  have h_st := Ne_0.of.Eq h_st
  have := NotInfinite.of.NeSt_0 h_st
  contradiction


-- created on 2025-12-11

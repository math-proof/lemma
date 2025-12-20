import Lemma.Hyperreal.EqSt_0.of.Infinite
import Lemma.Hyperreal.Infinite.is.InfiniteAdd.of.NotInfinite
import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Nat.Add
open Hyperreal Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : (a / b + b / a).st ≠ 0) :
-- imply
  ¬(a / b).Infinite := by
-- proof
  by_contra h_inf
  have h_eps := InfinitesimalDiv.of.InfiniteDiv h_inf
  have h_inf := InfiniteAdd.of.Infinite.NotInfinite (NotInfinite.of.Infinitesimal h_eps) h_inf
  have h_st := EqSt_0.of.Infinite h_inf
  rw [Add.comm] at h_st
  contradiction


-- created on 2025-12-20

import Lemma.Hyperreal.InfiniteDiv.of.Infinite.Ne_0
import Lemma.Hyperreal.InfiniteInfty
import Lemma.Hyperreal.Infinitesimal0
import Lemma.Hyperreal.InfinitesimalDiv.of.InfiniteDiv
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (r : ℝ)
  (h : x → ∞) :
-- imply
  (r / x) → 0 := by
-- proof
  if h_r : r = 0 then
    subst h_r
    simp
  else
    apply InfinitesimalDiv.of.InfiniteDiv
    apply InfiniteDiv.of.Infinite.Ne_0 h h_r


-- created on 2025-12-16

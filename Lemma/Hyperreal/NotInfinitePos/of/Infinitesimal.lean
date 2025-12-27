import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.Infinite.is.InfinitePos.ou.InfiniteNeg
open Hyperreal


@[main, mt]
private lemma main
  {x : ℝ*}
-- given
  (h : x.Infinitesimal) :
-- imply
  ¬x.InfinitePos := by
-- proof
  have h := NotInfinite.of.Infinitesimal h
  let ⟨h, h'⟩ := NotInfinitePos.NotInfiniteNeg.of.NotInfinite h
  assumption


-- created on 2025-12-27

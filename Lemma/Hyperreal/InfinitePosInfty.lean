import Lemma.Hyperreal.InfiniteInfty
open Hyperreal


@[path]
private lemma main :
-- imply
  Hyperreal.omega → +∞ :=
-- proof
  InfinitePos.of.Infinite.Gt_0 InfiniteInfty GtInfty0


-- created on 2025-12-29

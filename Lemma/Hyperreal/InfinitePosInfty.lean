import Lemma.Hyperreal.InfinitePos.is.Infinite.Gt_0
import Lemma.Hyperreal.InfiniteInfty
import Lemma.Hyperreal.GtInfty0
open Hyperreal


@[main]
private lemma main :
-- imply
  Hyperreal.omega.InfinitePos :=
-- proof
  InfinitePos.of.Infinite.Gt_0 InfiniteInfty GtInfty0


-- created on 2025-12-29

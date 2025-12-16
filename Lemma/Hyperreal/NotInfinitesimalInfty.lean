import Lemma.Hyperreal.NotInfinite.of.Infinitesimal
import Lemma.Hyperreal.InfiniteInfty
open Hyperreal


@[main]
private lemma main :
-- imply
  ¬Hyperreal.omega.Infinitesimal :=
-- proof
  NotInfinitesimal.of.Infinite InfiniteInfty


-- created on 2025-12-16

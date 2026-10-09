import Lemma.Hyperreal.EqSt_0.of.Infinitesimal
import Lemma.Hyperreal.Infinitesimal0
open Hyperreal


@[path]
private lemma main :
-- imply
  stdPart (0 : ℝ*) = 0 :=
-- proof
  EqSt_0.of.Infinitesimal Infinitesimal0


-- created on 2025-12-11

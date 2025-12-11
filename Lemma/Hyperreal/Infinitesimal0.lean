import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
open Hyperreal


@[main]
private lemma main :
-- imply
  Infinitesimal 0 := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  simp


-- created on 2025-12-09

import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FLTPrelim_Modularity


/--
[WeierstrassCurve_card_pos](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_card_pos.lean)
-/
@[path]
private lemma main
  [CommRing F] [Finite F]
  {W : WeierstrassCurve F} :
-- imply
  0 < W.card :=
-- proof
  Nat.card_pos


-- created on 2026-10-24

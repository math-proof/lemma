import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FLTPrelim_Modularity
import Def.WeierstrassCurve_VariableChangePointEquiv
open WeierstrassCurve


/-- ported from external source -/
@[path]
private lemma main
  [Field K] [DecidableEq K]
  {X Y : WeierstrassCurve K}
  {E : WeierstrassCurve.VariableChange K}
-- given
  (h : E • X = Y) :
-- imply
  Y.card = X.card :=
-- proof
  Nat.card_congr (WeierstrassCurve.Affine.Point.equivOfVariableChangeEq h)


-- created on 2026-10-24

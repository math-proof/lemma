import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.WeierstrassCurve.VeluPointMap
import Lemma.WeierstrassCurve.OddOrderSummingSet
import Lemma.Int.P2MUtil
open WeierstrassCurve Int
set_option warn.sorry false
set_option maxHeartbeats 800000


/--
[WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean)
-/
@[path]
private lemma main
  [Field L] [DecidableEq L] [IsAlgClosed L]
  {W : WeierstrassCurve L} [W.IsElliptic]
  {n : ℕ}
  {Q : W.toAffine.Point}
  {x y : L}
-- given
  (h0 : (2 : L) ≠ 0)
  (h1 : addOrderOf Q = 2 * n + 1)
  (h2 : W.toAffine.Equation x y)
  (h3 : ∀ A ∈ W.oddOrderSummingSet Q n, x ≠ A.1) :
-- imply
  (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.Equation
    (W.veluX (W.oddOrderSummingSet Q n) x) (W.veluY (W.oddOrderSummingSet Q n) x y) := by
-- proof
  obtain h | hn := Nat.eq_zero_or_pos n
  ·
    subst h
    have hempty : W.oddOrderSummingSet Q 0 = ∅ := by
      simp [WeierstrassCurve.oddOrderSummingSet]
    rwa [hempty, WeierstrassCurve.veluQuotient_empty, WeierstrassCurve.veluX_empty,
      WeierstrassCurve.veluY_empty]
  ·
    clear hn h0 h1 h3
    sorry


-- created on 2026-10-24

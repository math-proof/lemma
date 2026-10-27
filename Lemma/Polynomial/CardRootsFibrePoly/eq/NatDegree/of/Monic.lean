import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularCurve.FibrePoly
import Lemma.Int.P2MUtil

open Polynomial ModularCurve

/--
[ModularCurve_card_roots_fibrePoly_of_monic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_card_roots_fibrePoly_of_monic.lean)
-/
@[path]
private lemma main
  [Field K] [IsAlgClosed K]
  {Φ : Polynomial (Polynomial ℤ)}
  {a : K}
-- given
  (hΦ : Φ.Monic) :
-- imply
  Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by
-- proof
  rw [← (IsAlgClosed.splits (fibrePoly Φ a)).natDegree_eq_card_roots]
  exact hΦ.natDegree_map _


-- created on 2026-10-23

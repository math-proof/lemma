import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
open StatMech StatMech.Onsager


/--
[ons_summable_tupleProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean)
-/
@[path]
private lemma ons_summable_tupleProd_eq
  [RCLike K]
  {wt : alpha → K}
  {k : ℕ}
-- given
  (hwt : Summable wt) :
-- imply
  Summable (fun p : Fin k → alpha => ∏ i, wt (p i)) := by
-- proof
  apply StatMech.Onsager.ons_summable_tupleProd wt hwt k

/--
[ons_tsum_tupleProd_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean)
-/
@[path]
private lemma ons_tsum_tupleProd_eq_pow_eq
  [RCLike K]
  {wt : alpha → K}
  {k : ℕ}
-- given
  (hwt : Summable wt) :
-- imply
  (∑' p : Fin k → alpha, ∏ i, wt (p i)) = (∑' a, wt a) ^ k := by
-- proof
  apply StatMech.Onsager.ons_tsum_tupleProd_eq_pow wt hwt k

/--
[ons_summable_listSeriesTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean)
-/
@[path]
private lemma ons_summable_listSeriesTerm_eq
  {wt : alpha → ℂ}
-- given
  (hwt : Summable fun a => ‖wt a‖)
  (hsmall : ∑' a, ‖wt a‖ < 1) :
-- imply
  Summable (ons_listSeriesTerm wt) := by
-- proof
  apply StatMech.Onsager.ons_summable_listSeriesTerm wt hwt hsmall

/--
[ons_tsum_listSeriesTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean)
-/
@[path]
private lemma ons_tsum_listSeriesTerm_eq
  {wt : alpha → ℂ}
-- given
  (hwt : Summable fun a => ‖wt a‖)
  (hsmall : ∑' a, ‖wt a‖ < 1) :
-- imply
  (∑' l : List alpha, ons_listSeriesTerm wt l) = ∑' k : ℕ, (∑' a, wt a) ^ (k + 1) / (k + 1) := by
-- proof
  apply StatMech.Onsager.ons_tsum_listSeriesTerm wt hwt hsmall


-- created on 2026-10-23

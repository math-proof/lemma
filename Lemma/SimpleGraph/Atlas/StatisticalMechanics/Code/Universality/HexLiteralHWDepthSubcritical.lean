import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthSubcritical
open StatMech StatMech.Universality


/--
[hlhds_hexChiE_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthSubcritical.lean)
-/
@[path]
private lemma hlhds_hexChiE_lt_one_eq :
-- imply
  hexChiE < 1 := by
-- proof
  apply StatMech.Universality.hlhds_hexChiE_lt_one

/--
[hlhds_summable_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthSubcritical.lean)
-/
@[path]
private lemma hlhds_summable_of_local_eq
-- given
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
-- imply
  ∀ x, 0 < x → x < hexChiE → Summable (fun n => hlc_sawCountR hexAWStart 1 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlhds_summable_of_local hlocal


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.FormalGroup.NSeries
import Lemma.FormalGroup.DrinfeldBasis
import Def.FormalGroup_PointTransport
import Lemma.WeierstrassCurve.FormalGroupLaw
import Lemma.WeierstrassCurve.VariableChangeSeries
import Lemma.Int.P2MUtil
open FormalGroup IsLocalRing Int


/--
[WeierstrassCurve_variableChangeSeries_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_variableChangeSeries_one.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} :
-- imply
  W.variableChangeSeries 1 = PowerSeries.X := by
-- proof
  have hden : W.variableChangeDenom 1 = 1 := by
    simp [WeierstrassCurve.variableChangeDenom, WeierstrassCurve.VariableChange.one_def]
  rw [WeierstrassCurve.variableChangeSeries, hden]
  have hinv : PowerSeries.invOfUnit (1 : PowerSeries R) 1 = 1 := by
    have h := PowerSeries.mul_invOfUnit (1 : PowerSeries R) 1 (by simp)
    rwa [one_mul] at h
  rw [hinv]
  simp [WeierstrassCurve.VariableChange.one_def]


-- created on 2026-10-24

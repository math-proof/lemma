import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
open StatMech StatMech.Universality StatMech.Universality.HexWindingBound


/--
[hexW1_heading_eq_of_dvd_six_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_heading_eq_of_dvd_six_of_bound_eq
  {H : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hdvd : (6 : ℤ) ∣ (hexInfra_headAccum h0 ts - H))
  (hbound : |hexInfra_headAccum h0 ts - H| < 6) :
-- imply
  hexInfra_headAccum h0 ts = H := by
-- proof
  apply StatMech.Universality.hexW1_heading_eq_of_dvd_six_of_bound h0 H ts hdvd hbound

/--
[hexW1_heading_window_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_heading_window_of_eq_eq
  {H w : ℤ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (heq : hexInfra_headAccum h0 ts = H)
  (hHL : w ≤ H)
  (hHU : H < w + 6) :
-- imply
  w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6 := by
-- proof
  apply StatMech.Universality.hexW1_heading_window_of_eq h0 H w ts heq hHL hHU

/--
[hexW1_bound_does_not_force_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_bound_does_not_force_eq_eq
  {H : ℤ} :
-- imply
  |(H + 3) - H| < 6 ∧ (H + 3) ≠ H := by
-- proof
  apply StatMech.Universality.hexW1_bound_does_not_force_eq H

/--
[heading_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma heading_eq_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexWindingBound inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  hexInfra_headAccum h0 ts = S.H := by
-- proof
  apply StatMech.Universality.HexWindingBound.heading_eq S ts hadm

/--
[exits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma exits_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexWindingBound inRegion a h0 z} :
-- imply
  ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep S.H) ∧ (S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6) := by
-- proof
  apply StatMech.Universality.HexWindingBound.exits S

/--
[toBoundarySide_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma toBoundarySide_H_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexWindingBound inRegion a h0 z} :
-- imply
  S.toBoundarySide.H = S.H := by
-- proof
  apply StatMech.Universality.HexWindingBound.toBoundarySide_H S

/--
[toBoundarySide_w](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma toBoundarySide_w_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexWindingBound inRegion a h0 z} :
-- imply
  S.toBoundarySide.w = S.w := by
-- proof
  apply StatMech.Universality.HexWindingBound.toBoundarySide_w S

/--
[turning_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma turning_const_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexWindingBound inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.HexWindingBound.turning_const S ts hadm

/--
[hexW1_windingSidePhaseLock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_windingSidePhaseLock_eq
  {a : ℂ}
  {zt zb : ℂ}
  {σ x W r : ℝ}
  {Bt : HexWindingBound inRegion a h0 zt}
  {Bb : HexWindingBound inRegion a h0 zb}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hWt : (Real.pi / 3) * ((Bt.H : ℝ) - (h0 : ℝ)) = W)
  (hWb : (Real.pi / 3) * ((Bb.H : ℝ) - (h0 : ℝ)) = -W)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
-- imply
  parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexW1_windingSidePhaseLock inRegion a h0 zt zb σ x W r Bt Bb hWt hWb hreflt hreflb

/--
[hexW1_trivialWindingBound_toBoundarySide_heading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_trivialWindingBound_toBoundarySide_heading_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_headAccum h0 ([] : List ℤ) = (hexW1_trivialWindingBound a h0).toBoundarySide.H := by
-- proof
  apply StatMech.Universality.hexW1_trivialWindingBound_toBoundarySide_heading a h0

/--
[hexW1_trivialWindingBound_turning_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean)
-/
@[path]
private lemma hexW1_trivialWindingBound_turning_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
-- proof
  apply StatMech.Universality.hexW1_trivialWindingBound_turning_zero a h0


-- created on 2026-10-23

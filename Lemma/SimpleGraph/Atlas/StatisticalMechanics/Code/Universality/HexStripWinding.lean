import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexStripWinding
open StatMech StatMech.Universality StatMech.Universality.HexStripWinding


/--
[hexStripWinding_runningHead_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_runningHead_zero_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripWinding_runningHead h0 ts 0 = h0 := by
-- proof
  apply StatMech.Universality.hexStripWinding_runningHead_zero h0 ts

/--
[hexStripWinding_runningHead_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_runningHead_length_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  hexStripWinding_runningHead h0 ts ts.length = hexInfra_headAccum h0 ts := by
-- proof
  apply StatMech.Universality.hexStripWinding_runningHead_length h0 ts

/--
[hexStripWinding_runningHead_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_runningHead_succ_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ)
  (hk : k < ts.length) :
-- imply
  hexStripWinding_runningHead h0 ts (k + 1) = hexStripWinding_runningHead h0 ts k + ts[k] := by
-- proof
  apply StatMech.Universality.hexStripWinding_runningHead_succ h0 ts k hk

/--
[hexStripWinding_headAccum_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_headAccum_sub_eq
  {ts : List ℤ}
-- given
  (h0 H : ℤ) :
-- imply
  hexInfra_headAccum h0 ts - H = ts.sum - (H - h0) := by
-- proof
  apply StatMech.Universality.hexStripWinding_headAccum_sub h0 H ts

/--
[headAccum_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma headAccum_window_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  S.w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < S.w + 6 := by
-- proof
  apply StatMech.Universality.HexStripWinding.headAccum_window S ts hadm

/--
[bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma bound_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  |hexInfra_headAccum h0 ts - S.H| < 6 := by
-- proof
  apply StatMech.Universality.HexStripWinding.bound S ts hadm

/--
[heading_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma heading_eq_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hsideExit : hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = z + HexWalk.halfStep S.H) :
-- imply
  hexInfra_headAccum h0 ts = S.H := by
-- proof
  apply StatMech.Universality.HexStripWinding.heading_eq S ts hadm hsideExit

/--
[hexStripWinding_toWindingBound_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_toWindingBound_H_eq
  {a : ℂ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  (hsideExit)
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).H = S.H := by
-- proof
  apply StatMech.Universality.hexStripWinding_toWindingBound_H inRegion a h0 z S

/--
[hexStripWinding_toWindingBound_w](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_toWindingBound_w_eq
  {a : ℂ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  (hsideExit)
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexStripWinding_toWindingBound inRegion a h0 z S hsideExit).w = S.w := by
-- proof
  apply StatMech.Universality.hexStripWinding_toWindingBound_w inRegion a h0 z S

/--
[hexStripWinding_window_of_headingBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_window_of_headingBound_eq
  {a : ℂ}
  {z : ℂ}
  {w : ℤ}
-- given
  (h0 : ℤ)
  (inRegion : ℂ → Prop)
  (hbd : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k ∧ hexStripWinding_runningHead h0 ts k < w + 6) :
-- imply
  ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k ∧ hexStripWinding_runningHead h0 ts k < w + 6 := by
-- proof
  apply StatMech.Universality.hexStripWinding_window_of_headingBound a h0 z w inRegion hbd

/--
[hexStripWinding_no_full_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_no_full_turn_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexStripWinding inRegion a h0 z}
  {ts : List ℤ}
  {j k : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hj : j ≤ ts.length)
  (hk : k ≤ ts.length) :
-- imply
  hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts k + 6 := by
-- proof
  apply StatMech.Universality.hexStripWinding_no_full_turn S ts hadm j k hj hk

/--
[hexStripWinding_sidePhaseLock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_sidePhaseLock_eq
  {a : ℂ}
  {zt zb : ℂ}
  {σ x W r : ℝ}
  {St : HexStripWinding inRegion a h0 zt}
  {Sb : HexStripWinding inRegion a h0 zb}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hsexT : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zt → hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = zt + HexWalk.halfStep St.H)
  (hsexB : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt zb → hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts) = zb + HexWalk.halfStep Sb.H)
  (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = W)
  (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -W)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
-- imply
  parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexStripWinding_sidePhaseLock inRegion a h0 zt zb σ x W r St Sb hsexT hsexB hWt hWb hreflt hreflb

/--
[hexStripWinding_trivial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_trivial_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  |hexInfra_headAccum h0 ([] : List ℤ) - (hexStripWinding_trivial a h0).H| < 6 := by
-- proof
  apply StatMech.Universality.hexStripWinding_trivial_bound a h0

/--
[hexStripWinding_window_of_boundedPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_window_of_boundedPrefixSum_eq
  {ts : List ℤ}
-- given
  (h0 lo : ℤ)
  (hps : ∀ k, k ≤ ts.length → lo ≤ (ts.take k).sum ∧ (ts.take k).sum < lo + 6) :
-- imply
  ∀ k, k ≤ ts.length → (h0 + lo) ≤ hexStripWinding_runningHead h0 ts k ∧ hexStripWinding_runningHead h0 ts k < (h0 + lo) + 6 := by
-- proof
  apply StatMech.Universality.hexStripWinding_window_of_boundedPrefixSum h0 lo ts hps

/--
[hexStripWinding_singleRight_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean)
-/
@[path]
private lemma hexStripWinding_singleRight_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (inReg : ℂ → Prop)
  (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg ∧ (HexWalk.ofTurns a h0 ts).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
  (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
-- imply
  |hexInfra_headAccum h0 [(-1 : ℤ)] - (hexStripWinding_singleRight a h0 inReg hclass).H| < 6 := by
-- proof
  apply StatMech.Universality.hexStripWinding_singleRight_bound a h0 inReg hclass hstay


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part5
open StatMech StatMech.Universality StatMech.Universality.HexStripBand


/--
[hexUmlauf_runningHead_step_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_runningHead_step_le_eq
  {a : ℂ}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (h0 : ℤ)
  (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
  (hk : k < ts.length) :
-- imply
  |hexStripWinding_runningHead h0 ts (k + 1) - hexStripWinding_runningHead h0 ts k| ≤ 1 := by
-- proof
  apply StatMech.Universality.hexUmlauf_runningHead_step_le a h0 ts hlegal k hk

/--
[hexUmlauf_runningHead_IVT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_runningHead_IVT_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  ∀ i j : ℕ, i ≤ j → j ≤ ts.length → ∀ m : ℤ, min (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) ≤ m → m ≤ max (hexStripWinding_runningHead h0 ts i) (hexStripWinding_runningHead h0 ts j) → ∃ c, i ≤ c ∧ c ≤ j ∧ hexStripWinding_runningHead h0 ts c = m := by
-- proof
  apply StatMech.Universality.hexUmlauf_runningHead_IVT a h0 ts hlegal

/--
[hexUmlauf_window_of_wall_noFullTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_window_of_wall_noFullTurn_eq
  {a : ℂ}
  {ts : List ℤ}
  {w : ℤ}
-- given
  (h0 : ℤ)
  (hlegal : (HexWalk.ofTurns a h0 ts).IsLegalSAW)
  (hwall : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k)
  (hnofull : ∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6)
  (hanchor : hexStripWinding_runningHead h0 ts 0 < w + 6) :
-- imply
  ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k ∧ hexStripWinding_runningHead h0 ts k < w + 6 := by
-- proof
  apply StatMech.Universality.hexUmlauf_window_of_wall_noFullTurn a h0 ts w hlegal hwall hnofull hanchor

/--
[windowField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma windowField_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {B : HexStripBand inRegion a h0 z}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hk : k ≤ ts.length) :
-- imply
  B.w ≤ hexStripWinding_runningHead h0 ts k ∧ hexStripWinding_runningHead h0 ts k < B.w + 6 := by
-- proof
  apply StatMech.Universality.HexStripBand.windowField B ts hadm k hk

/--
[hexUmlauf_stripWinding_of_band_H](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_stripWinding_of_band_H_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripBand inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexUmlauf_stripWinding_of_band inRegion a h0 z B).H = B.H := by
-- proof
  apply StatMech.Universality.hexUmlauf_stripWinding_of_band_H inRegion a h0 z B

/--
[hexUmlauf_stripWinding_of_band_w](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_stripWinding_of_band_w_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripBand inRegion a h0 z}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ) :
-- imply
  (hexUmlauf_stripWinding_of_band inRegion a h0 z B).w = B.w := by
-- proof
  apply StatMech.Universality.hexUmlauf_stripWinding_of_band_w inRegion a h0 z B

/--
[hexUmlauf_bound_of_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_bound_of_band_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripBand inRegion a h0 z}
  {ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  |hexInfra_headAccum h0 ts - B.H| < 6 := by
-- proof
  apply StatMech.Universality.hexUmlauf_bound_of_band inRegion a h0 z B ts hadm

/--
[hexUmlauf_band_trivial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_band_trivial_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  |hexInfra_headAccum h0 ([] : List ℤ) - (hexUmlauf_band_trivial a h0).H| < 6 := by
-- proof
  apply StatMech.Universality.hexUmlauf_band_trivial_bound a h0

/--
[hexUmlauf_band_singleRight_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_band_singleRight_bound_eq
  {a : ℂ}
-- given
  (h0 : ℤ)
  (inReg : ℂ → Prop)
  (hclass : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inReg ∧ (HexWalk.ofTurns a h0 ts).EndsAt (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) → ts = [(-1 : ℤ)])
  (hstay : (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn inReg) :
-- imply
  |hexInfra_headAccum h0 [(-1 : ℤ)] - (hexUmlauf_band_singleRight a h0 inReg hclass).H| < 6 := by
-- proof
  apply StatMech.Universality.hexUmlauf_band_singleRight_bound a h0 inReg hclass hstay

/--
[hexUmlauf_no_full_revolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWindingClose.lean)
-/
@[path]
private lemma hexUmlauf_no_full_revolution_eq
  {a : ℂ}
  {z : ℂ}
  {B : HexStripBand inRegion a h0 z}
  {ts : List ℤ}
  {k : ℕ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z)
  (hk : k ≤ ts.length) :
-- imply
  hexStripWinding_runningHead h0 ts k < B.w + 6 := by
-- proof
  apply StatMech.Universality.hexUmlauf_no_full_revolution inRegion a h0 z B ts hadm k hk


-- created on 2026-10-23

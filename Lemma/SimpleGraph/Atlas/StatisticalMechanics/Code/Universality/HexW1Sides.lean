import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
open StatMech StatMech.Universality StatMech.Universality.HexBoundarySide


/--
[hexW1_heading_sub_dvd_six_of_sideExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_heading_sub_dvd_six_of_sideExit_eq
  {a : ℂ}
  {z : ℂ}
  {H : ℤ}
  {ts₁ ts₂ : List ℤ}
-- given
  (h0 : ℤ)
  (hz₁ : (HexWalk.ofTurns a h0 ts₁).EndsAt z)
  (hv₁ : hexInfra_midAccum a h0 ts₁ + HexWalk.halfStep (hexInfra_headAccum h0 ts₁) = z + HexWalk.halfStep H)
  (hz₂ : (HexWalk.ofTurns a h0 ts₂).EndsAt z)
  (hv₂ : hexInfra_midAccum a h0 ts₂ + HexWalk.halfStep (hexInfra_headAccum h0 ts₂) = z + HexWalk.halfStep H) :
-- imply
  (6 : ℤ) ∣ (hexInfra_headAccum h0 ts₁ - hexInfra_headAccum h0 ts₂) := by
-- proof
  apply StatMech.Universality.hexW1_heading_sub_dvd_six_of_sideExit a h0 z H ts₁ ts₂ hz₁ hv₁ hz₂ hv₂

/--
[heading_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma heading_det_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexBoundarySide inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  hexInfra_headAccum h0 ts = S.H := by
-- proof
  apply StatMech.Universality.HexBoundarySide.heading_det S ts hadm

/--
[turning_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma turning_const_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexBoundarySide inRegion a h0 z}
  {ts : List ℤ}
-- given
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) :
-- imply
  (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.HexBoundarySide.turning_const S ts hadm

/--
[hdet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hdet_eq
  {inRegion : ℂ → Prop}
  {a : ℂ}
  {h0 : ℤ}
  {z : ℂ}
  {S : HexBoundarySide inRegion a h0 z} :
-- imply
  ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn inRegion ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = (Real.pi / 3) * ((S.H : ℝ) - (h0 : ℝ)) := by
-- proof
  apply StatMech.Universality.HexBoundarySide.hdet S

/--
[hexW1_sidePhaseLock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_sidePhaseLock_eq
  {a : ℂ}
  {zt zb : ℂ}
  {σ x W r : ℝ}
  {St : HexBoundarySide inRegion a h0 zt}
  {Sb : HexBoundarySide inRegion a h0 zb}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = W)
  (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -W)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
-- imply
  parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexW1_sidePhaseLock inRegion a h0 zt zb σ x W r St Sb hWt hWb hreflt hreflb

/--
[hexW1_bottomSide_phaseLock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_bottomSide_phaseLock_eq
  {a : ℂ}
  {zt zb : ℂ}
  {x r : ℝ}
  {St : HexBoundarySide inRegion a h0 zt}
  {Sb : HexBoundarySide inRegion a h0 zb}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hWt : (Real.pi / 3) * ((St.H : ℝ) - (h0 : ℝ)) = Real.pi)
  (hWb : (Real.pi / 3) * ((Sb.H : ℝ) - (h0 : ℝ)) = -Real.pi)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
-- imply
  parafObservable inRegion a h0 zt (5 / 8) x + parafObservable inRegion a h0 zb (5 / 8) x = ((-(2 * hexBdryCl) * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexW1_bottomSide_phaseLock inRegion a h0 zt zb x r St Sb hWt hWb hreflt hreflb

/--
[hexW1_hexUnit_add_int](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_hexUnit_add_int_eq
-- given
  (h t : ℤ) :
-- imply
  hexUnit (h + t) = hexUnit h * Complex.exp (Complex.I * ((t : ℝ) * (Real.pi / 3))) := by
-- proof
  apply StatMech.Universality.hexW1_hexUnit_add_int h t

/--
[hexW1_halfStep_add_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_halfStep_add_ne_zero_eq
-- given
  (h t : ℤ)
  (ht : t = 1 ∨ t = -1) :
-- imply
  HexWalk.halfStep h + HexWalk.halfStep (h + t) ≠ 0 := by
-- proof
  apply StatMech.Universality.hexW1_halfStep_add_ne_zero h t ht

/--
[hexW1_singleton_admissible_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_singleton_admissible_nil_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hadm : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn (fun m => m = a) ∧ (HexWalk.ofTurns a h0 ts).EndsAt a) :
-- imply
  ts = [] := by
-- proof
  apply StatMech.Universality.hexW1_singleton_admissible_nil a h0 ts hadm

/--
[hexW1_trivialSide_turning_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1Sides.lean)
-/
@[path]
private lemma hexW1_trivialSide_turning_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
-- proof
  apply StatMech.Universality.hexW1_trivialSide_turning_zero a h0


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexInfraCut
open StatMech StatMech.Universality


/--
[hexInfra_headAccum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_headAccum_append_eq
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_headAccum h (s ++ t) = hexInfra_headAccum (hexInfra_headAccum h s) t := by
-- proof
  apply StatMech.Universality.hexInfra_headAccum_append h s t

/--
[hexInfra_stepReSum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_stepReSum_append_eq
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_stepReSum h (s ++ t) = hexInfra_stepReSum h s + hexInfra_stepReSum (hexInfra_headAccum h s) t := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_append h s t

/--
[hexInfra_stepReSum_take_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_stepReSum_take_drop_eq
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_stepReSum h0 ts = hexInfra_stepReSum h0 (ts.take cp) + hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp) := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_take_drop h0 ts cp

/--
[hexInfra_prefix_reachesWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_prefix_reachesWidth_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hdisp : (T : ℝ) ≤ hexInfra_stepReSum h0 (ts.take cp) + (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take cp))).re) :
-- imply
  hexWall3_ReachesWidth a h0 T (ts.take cp) := by
-- proof
  apply StatMech.Universality.hexInfra_prefix_reachesWidth a h0 T ts cp hdisp

/--
[hexInfra_suffix_displacement_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_suffix_displacement_eq_eq
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take cp)) (ts.drop cp) = hexInfra_stepReSum h0 ts - hexInfra_stepReSum h0 (ts.take cp) := by
-- proof
  apply StatMech.Universality.hexInfra_suffix_displacement_eq h0 ts cp

/--
[hexInfra_cut_displacement_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraCut.lean)
-/
@[path]
private lemma hexInfra_cut_displacement_witness_eq
-- given
  (h0 : ℤ) :
-- imply
  hexInfra_stepReSum h0 [(-1 : ℤ), 1] = hexInfra_stepReSum h0 ([(-1 : ℤ), 1].take 1) + hexInfra_stepReSum (hexInfra_headAccum h0 ([(-1 : ℤ), 1].take 1)) ([(-1 : ℤ), 1].drop 1) := by
-- proof
  apply StatMech.Universality.hexInfra_cut_displacement_witness h0


-- created on 2026-10-23

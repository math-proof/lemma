import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexInfraDisplacement
open StatMech StatMech.Universality


/--
[hexInfra_midAccum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_midAccum_nil_eq
  {m : ℂ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_midAccum m h [] = m := by
-- proof
  apply StatMech.Universality.hexInfra_midAccum_nil m h

/--
[hexInfra_midAccum_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_midAccum_cons_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexInfra_midAccum m h (t :: ts) = hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts := by
-- proof
  apply StatMech.Universality.hexInfra_midAccum_cons m h t ts

/--
[hexInfra_headAccum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_headAccum_nil_eq
-- given
  (h : ℤ) :
-- imply
  hexInfra_headAccum h [] = h := by
-- proof
  apply StatMech.Universality.hexInfra_headAccum_nil h

/--
[hexInfra_headAccum_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_headAccum_cons_eq
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexInfra_headAccum h (t :: ts) = hexInfra_headAccum (h + t) ts := by
-- proof
  apply StatMech.Universality.hexInfra_headAccum_cons h t ts

/--
[hexInfra_verticesAux_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_verticesAux_ne_nil_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  HexWalk.verticesAux m h ts ≠ [] := by
-- proof
  apply StatMech.Universality.hexInfra_verticesAux_ne_nil m h ts

/--
[hexInfra_verticesAux_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_verticesAux_getLast_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (HexWalk.verticesAux m h ts).getLast? = some (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) := by
-- proof
  apply StatMech.Universality.hexInfra_verticesAux_getLast m h ts

/--
[hexInfra_verticesAux_getLast_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_verticesAux_getLast_mem_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts) ∈ HexWalk.verticesAux m h ts := by
-- proof
  apply StatMech.Universality.hexInfra_verticesAux_getLast_mem m h ts

/--
[hexInfra_stepReSum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepReSum_nil_eq
-- given
  (h : ℤ) :
-- imply
  hexInfra_stepReSum h [] = 0 := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_nil h

/--
[hexInfra_stepReSum_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepReSum_cons_eq
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexInfra_stepReSum h (t :: ts) = (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re + hexInfra_stepReSum (h + t) ts := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_cons h t ts

/--
[hexInfra_midAccum_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_midAccum_re_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexInfra_midAccum m h ts).re = m.re + hexInfra_stepReSum h ts := by
-- proof
  apply StatMech.Universality.hexInfra_midAccum_re m h ts

/--
[hexInfra_ofTurns_last_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_ofTurns_last_re_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)).re = a.re + hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re := by
-- proof
  apply StatMech.Universality.hexInfra_ofTurns_last_re a h0 ts

/--
[hexInfra_halfStep_re_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_halfStep_re_abs_le_eq
-- given
  (h : ℤ) :
-- imply
  |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
-- proof
  apply StatMech.Universality.hexInfra_halfStep_re_abs_le h

/--
[hexInfra_halfStep_re_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_halfStep_re_le_eq
-- given
  (h : ℤ) :
-- imply
  (HexWalk.halfStep h).re ≤ 1 / 2 := by
-- proof
  apply StatMech.Universality.hexInfra_halfStep_re_le h

/--
[hexInfra_stepReSum_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepReSum_le_length_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_stepReSum h ts ≤ ts.length := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_le_length h ts

/--
[hexInfra_verticesAux_last_re_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_verticesAux_last_re_le_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)).re ≤ m.re + (ts.length + 1) := by
-- proof
  apply StatMech.Universality.hexInfra_verticesAux_last_re_le m h ts

/--
[hexInfra_stepIncrements_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepIncrements_nil_eq
-- given
  (h : ℤ) :
-- imply
  hexInfra_stepIncrements h [] = [] := by
-- proof
  apply StatMech.Universality.hexInfra_stepIncrements_nil h

/--
[hexInfra_stepIncrements_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepIncrements_cons_eq
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  hexInfra_stepIncrements h (t :: ts) = ((HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re) :: hexInfra_stepIncrements (h + t) ts := by
-- proof
  apply StatMech.Universality.hexInfra_stepIncrements_cons h t ts

/--
[hexInfra_stepReSum_eq_sum_increments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepReSum_eq_sum_increments_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexInfra_stepReSum h ts = (hexInfra_stepIncrements h ts).sum := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_eq_sum_increments h ts

/--
[hexInfra_stepReSum_ge_of_advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_stepReSum_ge_of_advance_eq
  {ts : List ℤ}
  {δ : ℝ}
-- given
  (h : ℤ)
  (hadv : ∀ x ∈ hexInfra_stepIncrements h ts, δ ≤ x) :
-- imply
  (δ * ts.length : ℝ) ≤ hexInfra_stepReSum h ts := by
-- proof
  apply StatMech.Universality.hexInfra_stepReSum_ge_of_advance h ts δ hadv

/--
[hexInfra_reachesWidth_of_last_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_reachesWidth_of_last_re_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hdisp : (T : ℝ) ≤ hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re) :
-- imply
  hexWall3_ReachesWidth a h0 T ts := by
-- proof
  apply StatMech.Universality.hexInfra_reachesWidth_of_last_re a h0 T ts hdisp

/--
[hexInfra_reachesWidth_of_advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_reachesWidth_of_advance_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
  {δ : ℝ}
-- given
  (h0 : ℤ)
  (hadv : ∀ x ∈ hexInfra_stepIncrements h0 ts, δ ≤ x)
  (hlast : 0 ≤ (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re)
  (hsteps : (T : ℝ) ≤ δ * ts.length) :
-- imply
  hexWall3_ReachesWidth a h0 T ts := by
-- proof
  apply StatMech.Universality.hexInfra_reachesWidth_of_advance a h0 T ts δ hadv hlast hsteps

/--
[hexInfra_singleRight_stepReSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_singleRight_stepReSum_eq :
-- imply
  hexInfra_stepReSum 0 [(-1 : ℤ)] + (HexWalk.halfStep (hexInfra_headAccum 0 [(-1 : ℤ)])).re = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_stepReSum

/--
[hexInfra_singleRight_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInfraDisplacement.lean)
-/
@[path]
private lemma hexInfra_singleRight_reaches_eq
  {a : ℂ} :
-- imply
  hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexInfra_singleRight_reaches a


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
open StatMech StatMech.Universality


/--
[hexSAWwt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexSAWwt_nonneg_eq
  {a : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexSAWwt a h0 x ts := by
-- proof
  apply StatMech.Universality.hexSAWwt_nonneg a h0 hx ts

/--
[hexSAWwt_of_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexSAWwt_of_isLegalSAW_eq
  {a : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
-- imply
  hexSAWwt a h0 x ts = x ^ (HexWalk.ofTurns a h0 ts).numVertices := by
-- proof
  apply StatMech.Universality.hexSAWwt_of_isLegalSAW a h0 x h

/--
[hexHalfStep_re_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexHalfStep_re_abs_eq
-- given
  (h : ℤ) :
-- imply
  |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
-- proof
  apply StatMech.Universality.hexHalfStep_re_abs h

/--
[hexVerticesAux_re_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexVerticesAux_re_le_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  ∀ v ∈ HexWalk.verticesAux m h ts, v.re ≤ m.re + (ts.length + 1 : ℝ) := by
-- proof
  apply StatMech.Universality.hexVerticesAux_re_le m h ts

/--
[hexReachWidth_len_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexReachWidth_len_ge_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hreach : ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
-- imply
  T ≤ (HexWalk.ofTurns a h0 ts).numVertices := by
-- proof
  apply StatMech.Universality.hexReachWidth_len_ge a h0 T ts hreach

/--
[hexColumnOfWidth_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexColumnOfWidth_colSum_eq
  {a : ℂ}
  {T : ℕ}
  {χ : ℝ}
  (hreach hsummable hle_one)
  {y : ℝ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop) :
-- imply
  (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum y = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := by
-- proof
  apply StatMech.Universality.hexColumnOfWidth_colSum a h0 T χ mem y

/--
[hexContourEmbOfPred_wtSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexContourEmbOfPred_wtSAW_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (P : List ℤ → Prop) :
-- imply
  (hexContourEmbOfPred a h0 hx P).wtSAW = hexSAWwt a h0 x := by
-- proof
  apply StatMech.Universality.hexContourEmbOfPred_wtSAW a h0 hx P

/--
[hexContourEmbOfPred_wtContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexContourEmbOfPred_wtContour_eq
  {a : ℂ}
  {x : ℝ}
  {i : {ts : List ℤ // P ts}}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (P : List ℤ → Prop) :
-- imply
  (hexContourEmbOfPred a h0 hx P).wtContour i = hexSAWwt a h0 x i.1 := by
-- proof
  apply StatMech.Universality.hexContourEmbOfPred_wtContour a h0 hx P i

/--
[hexColumnEmbOfPred_wtSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexColumnEmbOfPred_wtSAW_eq
  {a : ℂ}
  {x : ℝ}
  {scale : {ts : List ℤ // P ts} → ℕ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (P : List ℤ → Prop) :
-- imply
  (hexColumnEmbOfPred a h0 hx P scale).wtSAW = hexSAWwt a h0 x := by
-- proof
  apply StatMech.Universality.hexColumnEmbOfPred_wtSAW a h0 hx P scale

/--
[hexSplitAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexSplitAt_injective_eq
  {cp : List ℤ → ℕ} :
-- imply
  Function.Injective (hexSplitAt cp) := by
-- proof
  apply StatMech.Universality.hexSplitAt_injective cp

/--
[hexHighestCutSplit_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexHighestCutSplit_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hexSplitAt (hexCutPos a h0)) := by
-- proof
  apply StatMech.Universality.hexHighestCutSplit_injective a h0

/--
[hexHWDecomp_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexInjections.lean)
-/
@[path]
private lemma hexHWDecomp_injective_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hexSplitAt (hexHWCutPos a h0)) := by
-- proof
  apply StatMech.Universality.hexHWDecomp_injective a h0


-- created on 2026-10-23

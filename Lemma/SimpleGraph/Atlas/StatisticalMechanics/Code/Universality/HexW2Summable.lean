import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexW2Summable
open StatMech StatMech.Universality


/--
[hexW2S_verticesAux_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_verticesAux_translate_eq
  {c m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  HexWalk.verticesAux (m + c) h ts = (HexWalk.verticesAux m h ts).map (· + c) := by
-- proof
  apply StatMech.Universality.hexW2S_verticesAux_translate c m h ts

/--
[hexW2S_isSAW_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_isSAW_translate_eq
  {c m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (HexWalk.ofTurns (m + c) h ts).IsSAW ↔ (HexWalk.ofTurns m h ts).IsSAW := by
-- proof
  apply StatMech.Universality.hexW2S_isSAW_translate c m h ts

/--
[hexW2S_isLegalSAW_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_isLegalSAW_translate_eq
  {c m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (HexWalk.ofTurns (m + c) h ts).IsLegalSAW ↔ (HexWalk.ofTurns m h ts).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexW2S_isLegalSAW_translate c m h ts

/--
[hexW2S_hexSAWwt_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_hexSAWwt_translate_eq
  {c m : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexSAWwt (m + c) h x ts = hexSAWwt m h x ts := by
-- proof
  apply StatMech.Universality.hexW2S_hexSAWwt_translate c m h x ts

/--
[hexW2S_hexSAWwt_mid_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_hexSAWwt_mid_indep_eq
  {m m' : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  hexSAWwt m' h x ts = hexSAWwt m h x ts := by
-- proof
  apply StatMech.Universality.hexW2S_hexSAWwt_mid_indep m m' h x ts

/--
[hexW2S_hexSAWwt_mono_fugacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_hexSAWwt_mono_fugacity_eq
  {a : ℂ}
  {x χ : ℝ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hxχ : x ≤ χ) :
-- imply
  hexSAWwt a h0 x ts ≤ hexSAWwt a h0 χ ts := by
-- proof
  apply StatMech.Universality.hexW2S_hexSAWwt_mono_fugacity a h0 hx hxχ ts

/--
[hexW2S_diff_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_diff_summable_eq
  {a : ℂ}
  {x χ : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hxχ : x ≤ χ)
  (memD : List ℤ → Prop)
  (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 χ d.1)) :
-- imply
  Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) := by
-- proof
  apply StatMech.Universality.hexW2S_diff_summable a h0 hx hxχ memD hDcrit

/--
[hexW2S_trivialHalf_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_trivialHalf_wt_eq
  {mid : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexW2_halfWt x ⟨mid, h0, []⟩ = x := by
-- proof
  apply StatMech.Universality.hexW2S_trivialHalf_wt mid h0 x

/--
[hexW2S_halfWt_not_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_halfWt_not_summable_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  ¬ Summable (hexW2_halfWt x) := by
-- proof
  apply StatMech.Universality.hexW2S_halfWt_not_summable hx

/--
[hexW2S_bridgeWt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_bridgeWt_nonneg_eq
  {x : ℝ}
  {b : HexW2SBridge}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexW2S_bridgeWt x b := by
-- proof
  apply StatMech.Universality.hexW2S_bridgeWt_nonneg hx b

/--
[hexW2S_bridgeWt_eq_halfWt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_bridgeWt_eq_halfWt_eq
  {x : ℝ}
  {mid : ℂ}
  {turns : List ℤ}
-- given
  (head : ℤ) :
-- imply
  hexW2S_bridgeWt x ⟨head, turns⟩ = hexW2_halfWt x ⟨mid, head, turns⟩ := by
-- proof
  apply StatMech.Universality.hexW2S_bridgeWt_eq_halfWt x mid head turns

/--
[hexW2S_bridge_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_bridge_summable_eq
  {x χ : ℝ}
-- given
  (hx : 0 ≤ x)
  (hxχ : x ≤ χ)
  (bridgeMem : ℤ × List ℤ → Prop)
  (hBcrit : Summable (fun b : {b // bridgeMem b} => hexSAWwt 0 b.1.1 χ b.1.2)) :
-- imply
  Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) := by
-- proof
  apply StatMech.Universality.hexW2S_bridge_summable hx hxχ bridgeMem hBcrit

/--
[hexW2S_diff_summable_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_diff_summable_of_finite_eq
  {a : ℂ}
  {x χ : ℝ}
  [Finite {ts // memD ts}]
-- given
  (h0 : ℤ)
  (hx : 0 ≤ x)
  (hxχ : x ≤ χ)
  (memD : List ℤ → Prop) :
-- imply
  Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) := by
-- proof
  apply StatMech.Universality.hexW2S_diff_summable_of_finite a h0 hx hxχ memD

/--
[hexW2S_bridge_summable_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Summable.lean)
-/
@[path]
private lemma hexW2S_bridge_summable_of_finite_eq
  {x χ : ℝ}
  [Finite {b // bridgeMem b}]
-- given
  (hx : 0 ≤ x)
  (hxχ : x ≤ χ)
  (bridgeMem : ℤ × List ℤ → Prop) :
-- imply
  Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) := by
-- proof
  apply StatMech.Universality.hexW2S_bridge_summable_of_finite hx hxχ bridgeMem


-- created on 2026-10-23

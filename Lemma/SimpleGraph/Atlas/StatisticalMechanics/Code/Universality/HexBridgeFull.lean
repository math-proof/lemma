import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBridgeFull
open StatMech StatMech.Universality


/--
[hxb_rungTurns_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_rungTurns_nil_eq :
-- imply
  hxb_rungTurns [] = [] := by
-- proof
  apply StatMech.Universality.hxb_rungTurns_nil

/--
[hxb_rungTurns_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_rungTurns_append_eq
  {γ δ : List (ℕ × ℤ)} :
-- imply
  hxb_rungTurns (γ ++ δ) = hxb_rungTurns γ ++ hxb_rungTurns δ := by
-- proof
  apply StatMech.Universality.hxb_rungTurns_append γ δ

/--
[hxb_rungTurns_rungs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_rungTurns_rungs_eq
  {b : HexBridge} :
-- imply
  hxb_rungTurns b.rungs = b.content := by
-- proof
  apply StatMech.Universality.hxb_rungTurns_rungs b

/--
[hxb_walkOf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_turns_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 γ).turns = hxb_rungTurns γ := by
-- proof
  apply StatMech.Universality.hxb_walkOf_turns a h0 γ

/--
[hxb_walkOf_startMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_startMid_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 γ).startMid = a := by
-- proof
  apply StatMech.Universality.hxb_walkOf_startMid a h0 γ

/--
[hxb_walkOf_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_h0_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 γ).h0 = h0 := by
-- proof
  apply StatMech.Universality.hxb_walkOf_h0 a h0 γ

/--
[hxb_walkOf_numVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_numVertices_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 γ).numVertices = γ.length + 1 := by
-- proof
  apply StatMech.Universality.hxb_walkOf_numVertices a h0 γ

/--
[hxb_walkOf_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_turning_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 γ).turning = (Real.pi / 3) * ((hxb_rungTurns γ).sum : ℝ) := by
-- proof
  apply StatMech.Universality.hxb_walkOf_turning a h0 γ

/--
[hxb_walkOfBridges_startMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_startMid_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 bs).startMid = a := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_startMid a h0 bs

/--
[hxb_walkOfBridges_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_h0_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 bs).h0 = h0 := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_h0 a h0 bs

/--
[hxb_walkOfBridges_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_turns_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 bs).turns = (bs.map HexBridge.content).flatten := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_turns a h0 bs

/--
[hxb_walkOfBridges_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_nil_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hxb_walkOfBridges a h0 [] = trivialWalk a h0 := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_nil a h0

/--
[hxb_walkOfBridges_numVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_numVertices_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 bs).numVertices = (bridgeRecompose bs).length + 1 := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_numVertices a h0 bs

/--
[hxb_walkOfBridges_turning_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_turning_cons_eq
  {a : ℂ}
  {b : HexBridge}
  {bs : List HexBridge}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 (b :: bs)).turning = (Real.pi / 3) * ((b.content).sum : ℝ) + (hxb_walkOfBridges a h0 bs).turning := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_turning_cons a h0 b bs

/--
[hxb_walkOf_legalTurns_of_legalRungs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_legalTurns_of_legalRungs_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ)
  (h : hxb_LegalRungs γ) :
-- imply
  (hxb_walkOf a h0 γ).LegalTurns := by
-- proof
  apply StatMech.Universality.hxb_walkOf_legalTurns_of_legalRungs a h0 γ h

/--
[hxb_legalRungs_recompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_legalRungs_recompose_eq
  {bs : List HexBridge}
-- given
  (h : hxb_LegalContents bs) :
-- imply
  hxb_LegalRungs (bridgeRecompose bs) := by
-- proof
  apply StatMech.Universality.hxb_legalRungs_recompose bs h

/--
[hxb_walkOfBridges_legalTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_legalTurns_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ)
  (h : hxb_LegalContents bs) :
-- imply
  (hxb_walkOfBridges a h0 bs).LegalTurns := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_legalTurns a h0 bs h

/--
[hxb_walkOfBridges_nil_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOfBridges_nil_isLegalSAW_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOfBridges a h0 []).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hxb_walkOfBridges_nil_isLegalSAW a h0

/--
[hxb_walkOf_nil_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_nil_isLegalSAW_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (hxb_walkOf a h0 []).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hxb_walkOf_nil_isLegalSAW a h0

/--
[hxb_walkOf_isLegalSAW_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_isLegalSAW_of_eq
  {a : ℂ}
  {bs : List HexBridge}
-- given
  (h0 : ℤ)
  (hlegal : hxb_LegalContents bs)
  (hsaw : (hxb_walkOfBridges a h0 bs).IsSAW) :
-- imply
  (hxb_walkOfBridges a h0 bs).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hxb_walkOf_isLegalSAW_of a h0 bs hlegal hsaw

/--
[hxb_walkOf_bridge_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_bridge_decomp_eq
  {bs : {bs : List HexBridge // StrictDecreasingWidths bs}}
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hxb_walkOf a h0 (hexHW_bridge_decomp bs : List (ℕ × ℤ)) = hxb_walkOfBridges a h0 bs.1 := by
-- proof
  apply StatMech.Universality.hxb_walkOf_bridge_decomp bs a h0

/--
[hxb_walkOf_valid_eq_bridges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeFull.lean)
-/
@[path]
private lemma hxb_walkOf_valid_eq_bridges_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ)
  (hv : hexHW_IsValidWalk γ) :
-- imply
  ∃ bs, StrictDecreasingWidths bs ∧ hxb_walkOf a h0 γ = hxb_walkOfBridges a h0 bs := by
-- proof
  apply StatMech.Universality.hxb_walkOf_valid_eq_bridges a h0 γ hv


-- created on 2026-10-23

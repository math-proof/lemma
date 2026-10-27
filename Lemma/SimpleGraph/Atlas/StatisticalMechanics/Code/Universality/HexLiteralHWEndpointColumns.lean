import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWEndpointColumns.Part2
open StatMech StatMech.Universality


/--
[hlhe_coordRun_height_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_coordRun_height_bounds_eq
  {p d : HexReturnCoord}
  {ts : List ℤ}
-- given
  (hd : d.IsUnit)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  -((ts.length : ℕ) : ℤ) ≤ (hlhr_coordRun p d ts).pos.x - (hlhr_coordRun p d ts).pos.y - (p.x - p.y) ∧ (hlhr_coordRun p d ts).pos.x - (hlhr_coordRun p d ts).pos.y - (p.x - p.y) ≤ (ts.length : ℕ) := by
-- proof
  apply StatMech.Universality.hlhe_coordRun_height_bounds p d ts hd hlegal

/--
[hlhe_latticeHeight_sub_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_latticeHeight_sub_bounds_eq
  {ts : List ℤ}
  {i j : ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns)
  (hij : i ≤ j)
  (hj : j ≤ ts.length) :
-- imply
  -(((j - i : ℕ) : ℤ)) ≤ hlhr_latticeHeight ts j - hlhr_latticeHeight ts i ∧ hlhr_latticeHeight ts j - hlhr_latticeHeight ts i ≤ ((j - i : ℕ) : ℤ) := by
-- proof
  apply StatMech.Universality.hlhe_latticeHeight_sub_bounds ts hlegal hij hj

/--
[hlhe_latticeWidth_le_intervalLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_latticeWidth_le_intervalLength_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns)
  (hp : p.1 ≤ p.2)
  (hp2 : p.2 ≤ ts.length) :
-- imply
  hlhr_latticeWidth ts p ≤ (hlhr_intervalContent ts p).length := by
-- proof
  apply StatMech.Universality.hlhe_latticeWidth_le_intervalLength ts hlegal p hp hp2

/--
[hlhe_literalBridge_width_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_literalBridge_width_le_length_eq
  {ts : List ℤ}
  {b : HexBridge}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts)
  (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf) :
-- imply
  b.width ≤ b.content.length := by
-- proof
  apply StatMech.Universality.hlhe_literalBridge_width_le_length ts hleg hhalf b hb

/--
[hlhe_literalBridge_weight_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_literalBridge_weight_decay_eq
  {ts : List ℤ}
  {b : HexBridge}
  {x : ℝ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts)
  (hb : b ∈ hlhr_literalBridgeList ts hleg hhalf)
  (hx : 0 ≤ x)
  (hxchi : x ≤ hexChiE) :
-- imply
  hhc_bridgeWeight x b ≤ (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b := by
-- proof
  apply StatMech.Universality.hlhe_literalBridge_weight_decay ts hleg hhalf b hb hx hxchi

/--
[hlhe_lowerActive_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_lowerActive_origin_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
-- given
  (hb : b ∈ hhs_activeBridges H.lowerImage) :
-- imply
  ∃ d : hhc_Dn a h0 N, b ∈ hlhr_literalBridgeList (H.lower d) (H.lower_legal d) (H.lower_halfSpace d) := by
-- proof
  apply StatMech.Universality.hlhe_lowerActive_origin H hb

/--
[hlhe_upperActive_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_upperActive_origin_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
-- given
  (hb : b ∈ hhs_activeBridges H.upperImage) :
-- imply
  ∃ d : hhc_Dn a h0 N, b ∈ hlhr_literalBridgeList (H.upper d) (H.upper_legal d) (H.upper_halfSpace d) := by
-- proof
  apply StatMech.Universality.hlhe_upperActive_origin H hb

/--
[hlhe_lowerActive_width_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_lowerActive_width_le_length_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
-- given
  (hb : b ∈ hhs_activeBridges H.lowerImage) :
-- imply
  b.width ≤ b.content.length := by
-- proof
  apply StatMech.Universality.hlhe_lowerActive_width_le_length H hb

/--
[hlhe_upperActive_width_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_upperActive_width_le_length_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
-- given
  (hb : b ∈ hhs_activeBridges H.upperImage) :
-- imply
  b.width ≤ b.content.length := by
-- proof
  apply StatMech.Universality.hlhe_upperActive_width_le_length H hb

/--
[hlhe_lowerActive_weight_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_lowerActive_weight_decay_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
  {x : ℝ}
-- given
  (hb : b ∈ hhs_activeBridges H.lowerImage)
  (hx : 0 ≤ x)
  (hxchi : x ≤ hexChiE) :
-- imply
  hhc_bridgeWeight x b ≤ (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b := by
-- proof
  apply StatMech.Universality.hlhe_lowerActive_weight_decay H hb hx hxchi

/--
[hlhe_upperActive_weight_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_upperActive_weight_decay_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {b : HexBridge}
  {x : ℝ}
-- given
  (hb : b ∈ hhs_activeBridges H.upperImage)
  (hx : 0 ≤ x)
  (hxchi : x ≤ hexChiE) :
-- imply
  hhc_bridgeWeight x b ≤ (x / hexChiE) ^ b.width * hhc_bridgeWeight hexChiE b := by
-- proof
  apply StatMech.Universality.hlhe_upperActive_weight_decay H hb hx hxchi

/--
[hlhe_positiveGeom_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_positiveGeom_summable_eq
  {r : ℝ}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r < 1) :
-- imply
  Summable (hlhe_positiveGeom r) := by
-- proof
  apply StatMech.Universality.hlhe_positiveGeom_summable hr0 hr1

/--
[hlhe_activeCriticalMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_activeCriticalMass_nonneg_eq
  {S : Finset HexHWContentHalf}
  {T : ℕ} :
-- imply
  0 ≤ hlhe_activeCriticalMass S T := by
-- proof
  apply StatMech.Universality.hlhe_activeCriticalMass_nonneg S T

/--
[hlhe_active_bridge_sum_le_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_active_bridge_sum_le_geom_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
-- given
  (hwidth : ∀ b ∈ hhs_activeBridges S, b.width ≤ b.content.length)
  (hmass : ∀ T, hlhe_activeCriticalMass S T ≤ 1)
  (hx : 0 ≤ x)
  (hxchi : x < hexChiE) :
-- imply
  (∑ b ∈ hhs_activeBridges S, hhc_bridgeWeight x b) ≤ ∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T := by
-- proof
  apply StatMech.Universality.hlhe_active_bridge_sum_le_geom S hwidth hmass hx hxchi

/--
[hlhe_half_sum_le_exp_geom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_half_sum_le_exp_geom_eq
  {S : Finset HexHWContentHalf}
  {x : ℝ}
-- given
  (hwidth : ∀ b ∈ hhs_activeBridges S, b.width ≤ b.content.length)
  (hmass : ∀ T, hlhe_activeCriticalMass S T ≤ 1)
  (hx : 0 ≤ x)
  (hxchi : x < hexChiE) :
-- imply
  ∑ s ∈ S, hhc_halfWeight x s ≤ Real.exp (∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T) := by
-- proof
  apply StatMech.Universality.hlhe_half_sum_le_exp_geom S hwidth hmass hx hxchi

/--
[hlhe_finite_partial_bound_of_critical_masses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWEndpointColumns.lean)
-/
@[path]
private lemma hlhe_finite_partial_bound_of_critical_masses_eq
  {a : ℂ}
  {N : ℕ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x)
  (hxchi : x < hexChiE)
  (hlower : ∀ T, hlhe_activeCriticalMass (hlha_augmentedTwoHalfData a h0 N).lowerImage T ≤ 1)
  (hupper : ∀ T, hlhe_activeCriticalMass (hlha_augmentedTwoHalfData a h0 N).upperImage T ≤ 1) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ 2)⁻¹ * Real.exp (2 * (∑' T : ℕ, hlhe_positiveGeom (x / hexChiE) T)) := by
-- proof
  apply StatMech.Universality.hlhe_finite_partial_bound_of_critical_masses a h0 N hx hxchi hlower hupper


-- created on 2026-10-23

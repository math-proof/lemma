import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
open StatMech StatMech.FrontierA


/--
[kw_principalTurnLift_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_principalTurnLift_add_eq
  {a b c : Real.Angle}
-- given
  (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
  (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
-- imply
  (c - a).toReal = (b - a).toReal + (c - b).toReal := by
-- proof
  apply StatMech.FrontierA.kw_principalTurnLift_add a b c hlower hupper

/--
[kwAngleTurnPhase_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwAngleTurnPhase_mul_eq
  {a b c : Real.Angle}
-- given
  (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
  (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
-- imply
  kwAngleTurnPhase a b * kwAngleTurnPhase b c = kwAngleTurnPhase a c := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_mul a b c hlower hupper

/--
[kwAngleTurnPhase_ear_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwAngleTurnPhase_ear_splice_eq
  {previous incoming diagonal outgoing next : Real.Angle}
-- given
  (hleftLower : -Real.pi < (incoming - previous).toReal + (diagonal - incoming).toReal)
  (hleftUpper : (incoming - previous).toReal + (diagonal - incoming).toReal ≤ Real.pi)
  (hmiddleLower : -Real.pi < (diagonal - incoming).toReal + (outgoing - diagonal).toReal)
  (hmiddleUpper : (diagonal - incoming).toReal + (outgoing - diagonal).toReal ≤ Real.pi)
  (hrightLower : -Real.pi < (outgoing - diagonal).toReal + (next - outgoing).toReal)
  (hrightUpper : (outgoing - diagonal).toReal + (next - outgoing).toReal ≤ Real.pi) :
-- imply
  kwAngleTurnPhase previous incoming * kwAngleTurnPhase incoming outgoing * kwAngleTurnPhase outgoing next = kwAngleTurnPhase previous diagonal * kwAngleTurnPhase diagonal next := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_ear_splice previous incoming diagonal outgoing next hleftLower hleftUpper hmiddleLower hmiddleUpper hrightLower hrightUpper

/--
[kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi_eq
  {a b c : Real.Angle}
-- given
  (hsign : (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧ 0 < (a - c).toReal) ∨ ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧ (a - c).toReal < 0)) :
-- imply
  (b - a).toReal + (c - b).toReal + (a - c).toReal = 2 * Real.pi ∨ (b - a).toReal + (c - b).toReal + (a - c).toReal = -(2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi a b c hsign

/--
[kw_three_principal_halfAngle_product_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_three_principal_halfAngle_product_eq_neg_one_eq
  {a b c : Real.Angle}
-- given
  (hsign : (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧ 0 < (a - c).toReal) ∨ ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧ (a - c).toReal < 0)) :
-- imply
  Complex.exp ((((b - a).toReal : ℂ) * Complex.I) / 2) * Complex.exp ((((c - b).toReal : ℂ) * Complex.I) / 2) * Complex.exp ((((a - c).toReal : ℂ) * Complex.I) / 2) = -1 := by
-- proof
  apply StatMech.FrontierA.kw_three_principal_halfAngle_product_eq_neg_one a b c hsign

/--
[kwComplexCross_cyclic_of_sum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwComplexCross_cyclic_of_sum_zero_eq
  {x y z : ℂ}
-- given
  (hsum : x + y + z = 0) :
-- imply
  kwComplexCross x y = kwComplexCross y z ∧ kwComplexCross y z = kwComplexCross z x := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_cyclic_of_sum_zero hsum

/--
[kw_collinear_of_cross_sub_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_collinear_of_cross_sub_eq_zero_eq
  {A B C : ℂ}
-- given
  (hcross : kwComplexCross (B - A) (C - B) = 0) :
-- imply
  Collinear ℝ ({A, B, C} : Set ℂ) := by
-- proof
  apply StatMech.FrontierA.kw_collinear_of_cross_sub_eq_zero hcross

/--
[kw_arg_div_pos_of_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_arg_div_pos_of_cross_pos_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hxy : 0 < kwComplexCross x y) :
-- imply
  0 < Complex.arg (y / x) := by
-- proof
  apply StatMech.FrontierA.kw_arg_div_pos_of_cross_pos hx hxy

/--
[kw_arg_div_neg_of_cross_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_arg_div_neg_of_cross_neg_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hxy : kwComplexCross x y < 0) :
-- imply
  Complex.arg (y / x) < 0 := by
-- proof
  apply StatMech.FrontierA.kw_arg_div_neg_of_cross_neg hx hxy

/--
[kw_angle_sub_toReal_eq_arg_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_angle_sub_toReal_eq_arg_div_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0) :
-- imply
  ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).toReal = Complex.arg (y / x) := by
-- proof
  apply StatMech.FrontierA.kw_angle_sub_toReal_eq_arg_div hx hy

/--
[kw_angle_sub_ne_pi_of_cross_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_angle_sub_ne_pi_of_cross_ne_zero_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hcross : kwComplexCross x y ≠ 0) :
-- imply
  (Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle) ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kw_angle_sub_ne_pi_of_cross_ne_zero hx hy hcross

/--
[kw_angle_sub_sign_of_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_angle_sub_sign_of_cross_pos_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hcross : 0 < kwComplexCross x y) :
-- imply
  ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).sign = 1 := by
-- proof
  apply StatMech.FrontierA.kw_angle_sub_sign_of_cross_pos hx hy hcross

/--
[kw_angle_sub_sign_of_cross_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_angle_sub_sign_of_cross_neg_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hcross : kwComplexCross x y < 0) :
-- imply
  ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).sign = -1 := by
-- proof
  apply StatMech.FrontierA.kw_angle_sub_sign_of_cross_neg hx hy hcross

/--
[kwAngleTurnPhase_mul_of_outer_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwAngleTurnPhase_mul_of_outer_sign_eq
  {a b c : Real.Angle}
-- given
  (hab : b - a ≠ (Real.pi : Real.Angle))
  (hbc : c - b ≠ (Real.pi : Real.Angle))
  (hsign : (b - a).sign = (c - a).sign) :
-- imply
  kwAngleTurnPhase a b * kwAngleTurnPhase b c = kwAngleTurnPhase a c := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_mul_of_outer_sign a b c hab hbc hsign

/--
[kwAngleTurnPhase_vector_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwAngleTurnPhase_vector_sum_eq
  {x y : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hcross : kwComplexCross x y ≠ 0) :
-- imply
  kwAngleTurnPhase (Complex.arg x : Real.Angle) (Complex.arg (x + y) : Real.Angle) * kwAngleTurnPhase (Complex.arg (x + y) : Real.Angle) (Complex.arg y : Real.Angle) = kwAngleTurnPhase (Complex.arg x : Real.Angle) (Complex.arg y : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_vector_sum hx hy hcross

/--
[kwAngleTurnPhase_ear_splice_vectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kwAngleTurnPhase_ear_splice_vectors_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hp : previous ≠ 0)
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hn : next ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hrightTurn : (Complex.arg next : Real.Angle) - (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
  (hleft : (0 < kwComplexCross previous incoming ∧ 0 < kwComplexCross previous (incoming + outgoing)) ∨ (kwComplexCross previous incoming < 0 ∧ kwComplexCross previous (incoming + outgoing) < 0))
  (hright : (0 < kwComplexCross (incoming + outgoing) outgoing ∧ 0 < kwComplexCross (incoming + outgoing) next) ∨ (kwComplexCross (incoming + outgoing) outgoing < 0 ∧ kwComplexCross (incoming + outgoing) next < 0)) :
-- imply
  kwAngleTurnPhase (Complex.arg previous : Real.Angle) (Complex.arg incoming : Real.Angle) * kwAngleTurnPhase (Complex.arg incoming : Real.Angle) (Complex.arg outgoing : Real.Angle) * kwAngleTurnPhase (Complex.arg outgoing : Real.Angle) (Complex.arg next : Real.Angle) = kwAngleTurnPhase (Complex.arg previous : Real.Angle) (Complex.arg (incoming + outgoing) : Real.Angle) * kwAngleTurnPhase (Complex.arg (incoming + outgoing) : Real.Angle) (Complex.arg next : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnPhase_ear_splice_vectors previous incoming outgoing next hp hi ho hn hmiddle hrightTurn hleft hright

/--
[kw_triangle_edgeAngles_same_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_triangle_edgeAngles_same_sign_eq
  {x y z : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (hsum : x + y + z = 0)
  (hcross : kwComplexCross x y ≠ 0) :
-- imply
  (0 < ((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).toReal ∧ 0 < ((Complex.arg z : Real.Angle) - (Complex.arg y : Real.Angle)).toReal ∧ 0 < ((Complex.arg x : Real.Angle) - (Complex.arg z : Real.Angle)).toReal) ∨ (((Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle)).toReal < 0 ∧ ((Complex.arg z : Real.Angle) - (Complex.arg y : Real.Angle)).toReal < 0 ∧ ((Complex.arg x : Real.Angle) - (Complex.arg z : Real.Angle)).toReal < 0) := by
-- proof
  apply StatMech.FrontierA.kw_triangle_edgeAngles_same_sign hx hy hz hsum hcross

/--
[kw_triangle_principal_phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma kw_triangle_principal_phaseProduct_eq_neg_one_eq
  {x y z : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (hsum : x + y + z = 0)
  (hcross : kwComplexCross x y ≠ 0) :
-- imply
  Complex.exp (((Complex.arg (y / x) : ℂ) * Complex.I) / 2) * Complex.exp (((Complex.arg (z / y) : ℂ) * Complex.I) / 2) * Complex.exp (((Complex.arg (x / z) : ℂ) * Complex.I) / 2) = -1 := by
-- proof
  apply StatMech.FrontierA.kw_triangle_principal_phaseProduct_eq_neg_one hx hy hz hsum hcross

/--
[KWStraightLineEmbedding.triangle_not_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma triangle_not_collinear_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d₀ d₁ d₂ : G.Dart}
-- given
  (h₀₁ : d₀.snd = d₁.fst)
  (h₁₂ : d₁.snd = d₂.fst)
  (h₂₀ : d₂.snd = d₀.fst) :
-- imply
  ¬Collinear ℝ ({embedding.vertex d₀.fst, embedding.vertex d₀.snd, embedding.vertex d₁.snd} : Set ℂ) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.triangle_not_collinear embedding d₀ d₁ d₂ h₀₁ h₁₂ h₂₀

/--
[KWStraightLineEmbedding.turnPhase_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean)
-/
@[path]
private lemma turnPhase_triangle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {d₀ d₁ d₂ : G.Dart}
-- given
  (h₀₁ : d₀.snd = d₁.fst)
  (h₁₂ : d₁.snd = d₂.fst)
  (h₂₀ : d₂.snd = d₀.fst) :
-- imply
  embedding.turnPhase d₀ d₁ * embedding.turnPhase d₁ d₂ * embedding.turnPhase d₂ d₀ = -1 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.turnPhase_triangle embedding d₀ d₁ d₂ h₀₁ h₁₂ h₂₀


-- created on 2026-10-23

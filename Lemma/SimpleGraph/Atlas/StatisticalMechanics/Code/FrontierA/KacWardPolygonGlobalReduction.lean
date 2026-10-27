import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
open Finset SimpleGraph Polynomial StatMech StatMech.FrontierA


/--
[kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D} :
-- imply
  kwLoopPhaseProduct (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = Complex.exp ((((∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) : ℂ) * Complex.I) / 2) := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum angle loop

/--
[kw_totalPrincipalTurn_eq_int_mul_two_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kw_totalPrincipalTurn_eq_int_mul_two_pi_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D} :
-- imply
  ∃ winding : ℤ, (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) = (winding : ℝ) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.kw_totalPrincipalTurn_eq_int_mul_two_pi angle loop

/--
[kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D}
  {winding : ℤ}
-- given
  (hturn : (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) = (winding : ℝ) * (2 * Real.pi))
  (hodd : Odd winding) :
-- imply
  kwLoopPhaseProduct (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = -1 := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_odd_winding angle loop winding hturn hodd

/--
[kw_odd_winding_of_angleTurnPhase_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kw_odd_winding_of_angleTurnPhase_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D}
  {winding : ℤ}
-- given
  (hturn : (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) = (winding : ℝ) * (2 * Real.pi))
  (hphase : kwLoopPhaseProduct (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = -1) :
-- imply
  Odd winding := by
-- proof
  apply StatMech.FrontierA.kw_odd_winding_of_angleTurnPhase_eq_neg_one angle loop winding hturn hphase

/--
[KWStraightLineCycleEarDecomposition.toPhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma toPhaseSign_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (h : KWStraightLineCycleEarDecomposition G embedding) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleEarDecomposition.toPhaseSign h

/--
[KWStraightLineCyclePhaseSign.of_exists_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma of_exists_removable_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hexists : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.of_exists_removable hexists embedding

/--
[KWStraightLineCyclePhaseSign.of_geometricEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma of_geometricEar_five_plus_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneGeometricEar (by omega)) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.of_geometricEar_five_plus hgeneric embedding

/--
[KWStraightLineCyclePhaseSign.of_alignedSideEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma of_alignedSideEar_five_plus_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneAlignedSideEar) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.of_alignedSideEar_five_plus hgeneric embedding

/--
[KWStraightLineCyclePhaseSign.of_strictParityEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma of_strictParityEar_five_plus_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneStrictParityEar) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.of_strictParityEar_five_plus hgeneric embedding

/--
[kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn_eq
  {n : ℕ}
  [NeZero n]
  {angle : D → Real.Angle}
  {loop : Fin n → D}
-- given
  (hturn : (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) = 2 * Real.pi ∨ (∑ k, (angle (loop (k + 1)) - angle (loop k)).toReal : ℝ) = -(2 * Real.pi)) :
-- imply
  kwLoopPhaseProduct (fun dart next ↦ kwAngleTurnPhase (angle dart) (angle next)) loop = -1 := by
-- proof
  apply StatMech.FrontierA.kwLoopPhaseProduct_angleTurnPhase_eq_neg_one_of_totalTurn angle loop hturn

/--
[KWStraightLineCycleTurning.phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma phaseProduct_eq_neg_one_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hturning : KWStraightLineCycleTurning G embedding)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleTurning.phaseProduct_eq_neg_one G embedding hturning p hp

/--
[KWStraightLineCycleOddTurning.phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma phaseProduct_eq_neg_one_eq_2
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hturning : KWStraightLineCycleOddTurning G embedding)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleOddTurning.phaseProduct_eq_neg_one G embedding hturning p hp

/--
[KWStraightLineCycleOddTurning.toPhaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma toPhaseSign_eq_2
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hturning : KWStraightLineCycleOddTurning G embedding) :
-- imply
  KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleOddTurning.toPhaseSign G embedding hturning

/--
[KWStraightLineCyclePhaseSign.toOddTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma toOddTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hsign : KWStraightLineCyclePhaseSign G embedding) :
-- imply
  KWStraightLineCycleOddTurning G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCyclePhaseSign.toOddTurning G embedding hsign

/--
[kw_straightLineCycleOddTurning_iff_phaseSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kw_straightLineCycleOddTurning_iff_phaseSign_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  KWStraightLineCycleOddTurning G embedding ↔ KWStraightLineCyclePhaseSign G embedding := by
-- proof
  apply StatMech.FrontierA.kw_straightLineCycleOddTurning_iff_phaseSign G embedding

/--
[KWStraightLineCycleTurning.toOddTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma toOddTurning_eq_2
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hturning : KWStraightLineCycleTurning G embedding) :
-- imply
  KWStraightLineCycleOddTurning G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleTurning.toOddTurning G embedding hturning

/--
[kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleOddTurning G embedding)
  (hp : p.IsCycle) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_cycle_eq_one_of_oddCycleTurning G embedding hdeg hturning p hp

/--
[kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleOddTurning G embedding) :
-- imply
  kwGraphFormalRoot G embedding.turnPhase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_oddCycleTurning G embedding hdeg hturning

/--
[kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleTurning G embedding)
  (hp : p.IsCycle) :
-- imply
  kwGraphFormalLogCoeff G embedding.turnPhase (ons_finsetExponent p.edges.toFinset) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGraphFormalLogCoeff_cycle_eq_one_of_cycleTurning G embedding hdeg hturning p hp

/--
[kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleTurning G embedding) :
-- imply
  kwGraphFormalRoot G embedding.turnPhase = kwGraphFormalEvenPolynomial G := by
-- proof
  apply StatMech.FrontierA.kw_straightLineGraph_formalRoot_eq_evenPolynomial_of_cycleTurning G embedding hdeg hturning

/--
[kacWard_straightLine_trivalent_of_cycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_of_cycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
  {q : ℝ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleTurning G embedding)
  (hq : 0 ≤ q)
  (hentry : ∀ dart next, ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤ q)
  (hcard : (Fintype.card G.Dart : ℝ) * q < 1) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_of_cycleTurning G embedding hdeg hturning weight q hq hentry hcard

/--
[kwDetScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwDetScalePolynomial_eval_eq
  [Fintype E]
  [DecidableEq E]
  {M : Matrix E E ℂ}
  {t : ℂ} :
-- imply
  (kwDetScalePolynomial M).eval t = (1 - t • M).det := by
-- proof
  apply StatMech.FrontierA.kwDetScalePolynomial_eval M t

/--
[kwEvenScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kwEvenScalePolynomial_eval_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {weight : Sym2 V → ℂ}
  {t : ℂ} :
-- imply
  (kwEvenScalePolynomial G weight).eval t = kwEvenPolynomial G (fun edge ↦ t * weight edge) := by
-- proof
  apply StatMech.FrontierA.kwEvenScalePolynomial_eval G weight t

/--
[kacWard_straightLine_trivalent_of_oddCycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_of_oddCycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleOddTurning G embedding) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_of_oddCycleTurning G embedding hdeg hturning weight

/--
[kacWard_straightLine_trivalent_allWeights_of_cycleTurning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonGlobalReduction.lean)
-/
@[path]
private lemma kacWard_straightLine_trivalent_allWeights_of_cycleTurning_eq
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {weight : Sym2 V → ℂ}
-- given
  (hdeg : ∀ vertex, G.degree vertex ≤ 3)
  (hturning : KWStraightLineCycleTurning G embedding) :
-- imply
  (1 - kwGraphTransition G weight embedding.turnPhase).det = (kwEvenPolynomial G weight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_straightLine_trivalent_allWeights_of_cycleTurning G embedding hdeg hturning weight


-- created on 2026-10-23

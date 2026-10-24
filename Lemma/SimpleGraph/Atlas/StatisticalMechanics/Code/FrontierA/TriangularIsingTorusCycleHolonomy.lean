import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy
open StatMech StatMech.FrontierA


/--
[triangularIntPos_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPos_zero_eq
  {n : Nat}
  [NeZero n]
-- given
  (direction : Fin n -> Fin 6) :
-- imply
  triangularIntPos direction 0 = 0 := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_zero direction

/--
[triangularIntPos_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPos_succ_eq
  {n : Nat}
  [NeZero n]
  {k : Fin n}
-- given
  (direction : Fin n -> Fin 6)
  (hclosed : ∑ i, triangularIntStep (direction i) = 0) :
-- imply
  triangularIntPos direction (k + 1) = triangularIntPos direction k + triangularIntStep (direction k) := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_succ direction hclosed k

/--
[triangularIntPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPoint_injective_eq :
-- imply
  Function.Injective triangularIntPoint := by
-- proof
  apply StatMech.FrontierA.triangularIntPoint_injective

/--
[triangularIntPoint_not_strictly_between_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPoint_not_strictly_between_step_eq
  {p q : Int × Int}
  {a : Fin 6}
-- given
  (hqp : q ≠ p)
  (hqend : q ≠ p + triangularIntStep a) :
-- imply
  ¬Sbtw Real (triangularIntPoint p) (triangularIntPoint q) (triangularIntPoint (p + triangularIntStep a)) := by
-- proof
  apply StatMech.FrontierA.triangularIntPoint_not_strictly_between_step p q a hqp hqend

/--
[triangular_open_intersection_edge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangular_open_intersection_edge_eq_eq
  {p q : Int × Int}
  {a b : Fin 6}
  {z : Complex}
-- given
  (hp : Sbtw Real (triangularIntPoint p) z (triangularIntPoint (p + triangularIntStep a)))
  (hq : Sbtw Real (triangularIntPoint q) z (triangularIntPoint (q + triangularIntStep b))) :
-- imply
  s(p, p + triangularIntStep a) = s(q, q + triangularIntStep b) := by
-- proof
  apply StatMech.FrontierA.triangular_open_intersection_edge_eq p q a b z hp hq

/--
[triangularIntPos_vertex_not_strictly_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPos_vertex_not_strictly_between_eq
  {n : Nat}
  [NeZero n]
  {i j : Fin n}
-- given
  (direction : Fin n -> Fin 6)
  (hclosed : ∑ i, triangularIntStep (direction i) = 0)
  (hinjective : Function.Injective (triangularIntPos direction))
  (hji : j ≠ i)
  (hjnext : j ≠ i + 1) :
-- imply
  ¬Sbtw Real (triangularIntPoint (triangularIntPos direction i)) (triangularIntPoint (triangularIntPos direction j)) (triangularIntPoint (triangularIntPos direction (i + 1))) := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_vertex_not_strictly_between direction hclosed hinjective i j hji hjnext

/--
[triangularIntPos_edgeInteriors_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularIntPos_edgeInteriors_disjoint_eq
  {n : Nat}
  [NeZero n]
  {i j : Fin n}
-- given
  (direction : Fin n -> Fin 6)
  (hclosed : ∑ i, triangularIntStep (direction i) = 0)
  (hn : 3 ≤ n)
  (hinjective : Function.Injective (triangularIntPos direction))
  (hij : i ≠ j) :
-- imply
  Disjoint {z : Complex | Sbtw Real (triangularIntPoint (triangularIntPos direction i)) z (triangularIntPoint (triangularIntPos direction (i + 1)))} {z : Complex | Sbtw Real (triangularIntPoint (triangularIntPos direction j)) z (triangularIntPoint (triangularIntPos direction (j + 1)))} := by
-- proof
  apply StatMech.FrontierA.triangularIntPos_edgeInteriors_disjoint direction hclosed hn hinjective i j hij

/--
[triangularTorusGraphPhase_one_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusGraphPhase_one_one_apply_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {d e : (triangularTorusGraph L).Dart} :
-- imply
  triangularTorusGraphPhase L rho 1 1 d e = triangularKacWardTurnMatrix rho (triangularTorusGraphDartDirection L d) (triangularTorusGraphDartDirection L e) := by
-- proof
  apply StatMech.FrontierA.triangularTorusGraphPhase_one_one_apply L rho d e

/--
[triangularTorus_cycleDirection_nonbacktracking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorus_cycleDirection_nonbacktracking_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ forall k, triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)) ≠ triangularTorusDirectionReverse (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cycleDirection_nonbacktracking L p hp

/--
[triangularTorus_cyclePhaseProduct_eq_turnProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_turnProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = ∏ k, triangularKacWardTurnMatrix rho (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1))) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_turnProduct L rho p hp

/--
[triangularTorusTurnExponent_cast_eq_angleClass_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusTurnExponent_cast_eq_angleClass_sub_eq
  {a b : Fin 6}
-- given
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  (triangularTorusTurnExponent a b : ZMod 8) = triangularTorusDirectionAngleClass b - triangularTorusDirectionAngleClass a := by
-- proof
  apply StatMech.FrontierA.triangularTorusTurnExponent_cast_eq_angleClass_sub a b hne

/--
[exists_triangularTorusTurnExponent_sum_eq_eight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma exists_triangularTorusTurnExponent_sum_eq_eight_mul_eq
  {n : Nat}
  [NeZero n]
-- given
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : forall k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k)) :
-- imply
  ∃ m : Int, (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) = 8 * m := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorusTurnExponent_sum_eq_eight_mul direction hnonbacktracking

/--
[exists_triangularTorus_cycleTurnSum_eq_eight_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma exists_triangularTorus_cycleTurnSum_eq_eight_mul_eq
  {L : Nat}
  [Fact (2 < L)]
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ ∃ m : Int, (∑ k, triangularTorusTurnExponent (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)))) = 8 * m := by
-- proof
  apply StatMech.FrontierA.exists_triangularTorus_cycleTurnSum_eq_eight_mul L p hp

/--
[triangularTorusTurnRoot_pow_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusTurnRoot_pow_eight_eq
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  rho ^ 8 = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusTurnRoot_pow_eight rho hrho

/--
[triangularTorusTurnRoot_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusTurnRoot_ne_zero_eq
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  rho ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorusTurnRoot_ne_zero rho hrho

/--
[triangularKacWardTurnMatrix_eq_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularKacWardTurnMatrix_eq_zpow_eq
  {rho : Complex}
  {a b : Fin 6}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hne : b ≠ triangularTorusDirectionReverse a) :
-- imply
  triangularKacWardTurnMatrix rho a b = rho ^ triangularTorusTurnExponent a b := by
-- proof
  apply StatMech.FrontierA.triangularKacWardTurnMatrix_eq_zpow rho hrho a b hne

/--
[prod_triangularKacWardTurnMatrix_eq_zpow_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma prod_triangularKacWardTurnMatrix_eq_zpow_sum_eq
  {n : Nat}
  [NeZero n]
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : forall k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k)) :
-- imply
  (∏ k, triangularKacWardTurnMatrix rho (direction k) (direction (k + 1))) = rho ^ (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) := by
-- proof
  apply StatMech.FrontierA.prod_triangularKacWardTurnMatrix_eq_zpow_sum rho hrho direction hnonbacktracking

/--
[triangularTorusTurnRoot_zpow_even_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusTurnRoot_zpow_even_revolutions_eq
  {rho : Complex}
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  rho ^ (8 * (2 * m)) = 1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusTurnRoot_zpow_even_revolutions rho hrho m

/--
[triangularTorusTurnRoot_zpow_odd_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorusTurnRoot_zpow_odd_revolutions_eq
  {rho : Complex}
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  rho ^ (8 * (2 * m + 1)) = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusTurnRoot_zpow_odd_revolutions rho hrho m

/--
[prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions_eq
  {n : Nat}
  [NeZero n]
  {rho : Complex}
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : forall k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
  (hturn : (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) = 8 * (2 * m)) :
-- imply
  (∏ k, triangularKacWardTurnMatrix rho (direction k) (direction (k + 1))) = 1 := by
-- proof
  apply StatMech.FrontierA.prod_triangularKacWardTurnMatrix_eq_one_of_even_revolutions rho hrho direction hnonbacktracking m hturn

/--
[prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions_eq
  {n : Nat}
  [NeZero n]
  {rho : Complex}
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (direction : Fin n -> Fin 6)
  (hnonbacktracking : forall k, direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
  (hturn : (∑ k, triangularTorusTurnExponent (direction k) (direction (k + 1))) = 8 * (2 * m + 1)) :
-- imply
  (∏ k, triangularKacWardTurnMatrix rho (direction k) (direction (k + 1))) = -1 := by
-- proof
  apply StatMech.FrontierA.prod_triangularKacWardTurnMatrix_eq_neg_one_of_odd_revolutions rho hrho direction hnonbacktracking m hturn

/--
[triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  [NeZero p.darts.length]
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle)
  (hturn : (∑ k, triangularTorusTurnExponent (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m)) :
-- imply
  kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = 1 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions L rho hrho p hp m hturn

/--
[triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean)
-/
@[path]
private lemma triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions_eq
  {L : Nat}
  [Fact (2 < L)]
  {rho : Complex}
  {root : ZMod L × ZMod L}
  {p : (triangularTorusGraph L).Walk root root}
  [NeZero p.darts.length]
  {m : Int}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hp : p.IsCycle)
  (hturn : (∑ k, triangularTorusTurnExponent (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1)) :
-- imply
  kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1) (kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions L rho hrho p hp m hturn


-- created on 2026-10-23

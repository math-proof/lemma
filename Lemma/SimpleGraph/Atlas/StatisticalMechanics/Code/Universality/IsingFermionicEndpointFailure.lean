import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part26
open StatMech StatMech.Universality


/--
[sourceFailureOutputAt_vertical_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureOutputAt_vertical_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hqVertical : q.2.1 = 0 \/ q.2.1 = R) :
-- imply
  Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 24 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureOutputAt_vertical_diffusive_weight_le R level rho p q hstart hρ hbottom htop hqVertical

/--
[sourceFailureOutputAt_left_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureOutputAt_left_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hqLeft : q.1.1 = 0)
  (hρ : 0 < rho)
  (hlevel : rho ≤ level) :
-- imply
  Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureOutputAt_left_diffusive_weight_le R level rho p q hstart hqLeft hρ hlevel

/--
[sourceFailureOutputAt_boundary_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureOutputAt_boundary_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level < R)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureOutputAt_boundary_diffusive_weight_le R level rho p q hstart hρ hleft hlevelR hbottom htop hqBoundary

/--
[mirrorFailureOutputAt_boundary_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorFailureOutputAt_boundary_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hlevel : 0 < level)
  (hright : level + rho <= R)
  (hbottom : rho <= p'.2.1)
  (htop : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorFailureOutputAt_boundary_diffusive_weight_le R level rho p p' q hstart hmirror hρ hlevel hright hbottom htop hqBoundary

/--
[sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level < R)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hbottom' : rho <= p'.2.1)
  (htop' : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 936 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureAt_boundary_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hlevelR hright hhalf hbottom htop hbottom' htop' hqBoundary

/--
[lineFirstEndpoint_boundary_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma lineFirstEndpoint_boundary_weight_le_eq
  {n k : Nat}
  {start target : IsingLineBox n}
-- given
  (hk : 0 < k)
  (htarget : isingLineBoxBoundary n target) :
-- imply
  Nat.card (IsingLineFirstEndpointFamily n k start target) / (2 : Real) ^ k <= 2 / (k : Real) := by
-- proof
  apply StatMech.Universality.lineFirstEndpoint_boundary_weight_le n k start target hk htarget

/--
[natCard_orderedFarEndpoint_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma natCard_orderedFarEndpoint_eq_sum_eq
  {m n t : Nat}
  {start target : IsingLineBox n}
  {markX targetX : Int} :
-- imply
  Nat.card (IsingOrderedFarEndpointFamily m n t start target markX targetX) = ∑ k : Fin (t + 1), ∑ j : Fin k, Nat.card (IsingLineFarFirstBoundaryFamily m j) * Nat.card (IsingLineFirstEndpointFamily n k start target) * Nat.card (VerticalChoicePathFamily (k - j) markX targetX) * 4 ^ (t - (k : Nat)) := by
-- proof
  apply StatMech.Universality.natCard_orderedFarEndpoint_eq_sum m n t start target markX targetX

/--
[orderedFarEndpoint_weight_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma orderedFarEndpoint_weight_eq_sum_eq
  {m n t : Nat}
  {start target : IsingLineBox n}
  {markX targetX : Int} :
-- imply
  Nat.card (IsingOrderedFarEndpointFamily m n t start target markX targetX) / (4 : Real) ^ t = ∑ k : Fin (t + 1), ∑ j : Fin k, (Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ (j : Nat)) * (Nat.card (IsingLineFirstEndpointFamily n k start target) / (2 : Real) ^ (k : Nat)) * (Nat.card (VerticalChoicePathFamily (k - j) markX targetX) / (2 : Real) ^ ((k : Nat) - (j : Nat))) := by
-- proof
  apply StatMech.Universality.orderedFarEndpoint_weight_eq_sum m n t start target markX targetX

/--
[orderedFarEndpoint_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma orderedFarEndpoint_weight_le_eq
  {m n t : Nat}
  {start target : IsingLineBox n}
  {markX targetX : Int}
-- given
  (hm : 0 < m)
  (ht : t <= m * m)
  (htarget : isingLineBoxBoundary n target) :
-- imply
  Nat.card (IsingOrderedFarEndpointFamily m n t start target markX targetX) / (4 : Real) ^ t <= 7488 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.orderedFarEndpoint_weight_le m n t start target markX targetX hm ht htarget

/--
[orderedFarEndpoint_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma orderedFarEndpoint_diffusive_weight_le_eq
  {rho m n : Nat}
  {start target : IsingLineBox n}
  {markX targetX : Int}
-- given
  (hρ : 0 < rho)
  (hρm : rho <= m)
  (htarget : isingLineBoxBoundary n target) :
-- imply
  Nat.card (IsingOrderedFarEndpointFamily m n (rho * rho) start target markX targetX) / (4 : Real) ^ (rho * rho) <= 7488 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.orderedFarEndpoint_diffusive_weight_le rho m n start target markX targetX hρ hρm htarget

/--
[natCard_mirrorFailureAt_le_aligned_add_residual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma natCard_mirrorFailureAt_le_aligned_add_residual_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) <= Nat.card (IsingSourceFailureOutputAtFamily R t p q level) + Nat.card (IsingMirrorFailureOutputAtFamily R t p p' q level) + Nat.card (IsingMirrorOnlySourceOutputAtFamily R t p p' q level) := by
-- proof
  apply StatMech.Universality.natCard_mirrorFailureAt_le_aligned_add_residual R t p p' q level

/--
[choiceRun_boundary_output_data_endpointFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma choiceRun_boundary_output_data_endpointFailure_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
  {w : IsingLeapfrogChoiceStringFamily t}
-- given
  (hq : isingLeapfrogBoxBoundary R q)
  (hout : isingLeapfrogChoiceRun R p w.1 = q) :
-- imply
  exists k, k <= t /\ isingLeapfrogChoiceRun R p (w.1.take k) = q /\ forall l, l < k -> ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p (w.1.take l)) := by
-- proof
  apply StatMech.Universality.choiceRun_boundary_output_data_endpointFailure R t p q hq w hout

/--
[mirrorOnly_firstBoundary_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorOnly_firstBoundary_right_eq
  {R level t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p)) :
-- imply
  exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) (level : Int)) (j : Nat), isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int) (isingLeapfrogChoiceSteps w.1.1) = some split /\ j < split.before.length /\ (isingLeapfrogChoiceRun R p' ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) (level : Int) w.1).1.take j)).1.1 = R /\ ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) = 2 * (level : Int) - R /\ (forall l, l < j -> 2 * (level : Int) - R < ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\ ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\ (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p' ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) (level : Int) w.1).1.take l))) /\ IsingLeapfrogChoiceExecValid R p (w.1.1.take split.before.length) := by
-- proof
  apply StatMech.Universality.mirrorOnly_firstBoundary_right R level t p p' q hstart hmirror w

/--
[mirrorOnly_ordered_boundary_marks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorOnly_ordered_boundary_marks_eq
  {R level t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {w : IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  exists (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) (level : Int)) (j k : Nat), isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) (level : Int) (isingLeapfrogChoiceSteps w.1.1) = some split /\ j < k /\ k <= t /\ (isingLeapfrogChoiceRun R p' ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) (level : Int) w.1).1.take j)).1.1 = R /\ ((isingLeapfrogChoiceRun R p (w.1.1.take j)).1.1 : Int) = 2 * (level : Int) - R /\ (forall l, l < j -> 2 * (level : Int) - R < ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) /\ ((isingLeapfrogChoiceRun R p (w.1.1.take l)).1.1 : Int) < level) /\ (forall l, l < j -> ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p' ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) (level : Int) w.1).1.take l))) /\ isingLeapfrogChoiceRun R p (w.1.1.take k) = q /\ (forall l, l < k -> ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p (w.1.1.take l))) := by
-- proof
  apply StatMech.Universality.mirrorOnly_ordered_boundary_marks R level t p p' q hstart hmirror hq w

/--
[natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint_eq
  {R level t : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hlevelR : level <= R)
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) <= Nat.card (IsingOrderedFarEndpointFamily (R - level) R t p.2 q.2 (2 * (level : Int) - R) (q.1 : Int)) := by
-- proof
  apply StatMech.Universality.natCard_mirrorOnlySourceOutputAt_le_orderedFarEndpoint R level t p p' q hlevelR hstart hmirror hq

/--
[mirrorOnlySourceOutputAt_vertical_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorOnlySourceOutputAt_vertical_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hright : level + rho <= R)
  (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
-- imply
  Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 7488 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorOnlySourceOutputAt_vertical_diffusive_weight_le R level rho p p' q hstart hmirror hρ hright hqVertical

/--
[orderedFarHorizontalEndpoint_weight_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma orderedFarHorizontalEndpoint_weight_eq_sum_eq
  {m R t : Nat}
  {mark target : IsingLineBox R}
  {startY targetY : Int} :
-- imply
  Nat.card (IsingOrderedFarHorizontalEndpointFamily m R t mark target startY targetY) / (4 : Real) ^ t = ∑ k : Fin (t + 1), ∑ j : Fin k, (Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ (j : Nat)) * (Nat.card (IsingLineFirstEndpointFamily R (k - j) mark target) / (2 : Real) ^ ((k : Nat) - (j : Nat))) * (Nat.card (VerticalChoicePathFamily k startY targetY) / (2 : Real) ^ (k : Nat)) := by
-- proof
  apply StatMech.Universality.orderedFarHorizontalEndpoint_weight_eq_sum m R t mark target startY targetY

/--
[lineFirstEndpoint_partial_weight_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma lineFirstEndpoint_partial_weight_le_one_eq
  {n N : Nat}
  {start target : IsingLineBox n}
-- given
  (htarget : isingLineBoxBoundary n target) :
-- imply
  (∑ r ∈ Finset.range (N + 1), (Nat.card (IsingLineFirstEndpointFamily n r start target) : Real) / (2 : Real) ^ r) <= 1 := by
-- proof
  apply StatMech.Universality.lineFirstEndpoint_partial_weight_le_one n N start target htarget

/--
[orderedFarHorizontalEndpoint_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma orderedFarHorizontalEndpoint_weight_le_eq
  {m R t : Nat}
  {mark target : IsingLineBox R}
  {startY targetY : Int}
-- given
  (hm : 0 < m)
  (ht : t <= m * m)
  (htarget : isingLineBoxBoundary R target) :
-- imply
  Nat.card (IsingOrderedFarHorizontalEndpointFamily m R t mark target startY targetY) / (4 : Real) ^ t <= 468 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.orderedFarHorizontalEndpoint_weight_le m R t mark target startY targetY hm ht htarget

/--
[natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint_eq
  {R level t : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hlevelR : level <= R)
  (hhalf : R <= 2 * level)
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hq : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingMirrorOnlySourceOutputAtFamily R t p p' q (level : Int)) <= Nat.card (IsingOrderedFarHorizontalEndpointFamily (R - level) R t ⟨2 * level - R, by omega⟩ q.1 (p.2.1 : Int) (q.2.1 : Int)) := by
-- proof
  apply StatMech.Universality.natCard_mirrorOnlySourceOutputAt_le_orderedFarHorizontalEndpoint R level t p p' q hlevelR hhalf hstart hmirror hq

/--
[mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorOnlySourceOutputAt_horizontal_diffusive_weight_le R level rho p p' q hstart hmirror hρ hright hhalf hqHorizontal

/--
[mirrorOnlySourceOutputAt_boundary_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorOnlySourceOutputAt_boundary_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingMirrorOnlySourceOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 7488 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorOnlySourceOutputAt_boundary_diffusive_weight_le R level rho p p' q hstart hmirror hρ hright hhalf hqBoundary

/--
[mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hbottom' : rho <= p'.2.1)
  (htop' : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 8424 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorFailureAt_boundary_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hhalf hbottom htop hbottom' htop' hqBoundary

/--
[sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level <= R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho p q hstart hρ hleft hlevelR hqHorizontal

/--
[sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hqVertical : q.2.1 = 0 ∨ q.2.1 = R) :
-- imply
  Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 24 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceChoiceNoHitOutputAt_vertical_diffusive_weight_le R level rho p q hstart hρ hbottom htop hqVertical

/--
[sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level <= R)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingSourceChoiceNoHitOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceChoiceNoHitOutputAt_boundary_diffusive_weight_le R level rho p q hstart hρ hleft hlevelR hbottom htop hqBoundary

/--
[mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hright : level + rho <= R)
  (hbottom : rho <= p'.2.1)
  (htop : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorChoiceNoHitOutputAt_boundary_diffusive_weight_le R level rho p p' q hstart hmirror hρ hright hbottom htop hqBoundary

/--
[natCard_choiceNoHitAt_le_source_add_mirror](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma natCard_choiceNoHitAt_le_source_add_mirror_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) <= Nat.card (IsingSourceChoiceNoHitOutputAtFamily R t p q level) + Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R t p p' q level) := by
-- proof
  apply StatMech.Universality.natCard_choiceNoHitAt_le_source_add_mirror R t p p' q level

/--
[choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hbottom' : rho <= p'.2.1)
  (htop' : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 936 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.choiceNoHitAt_boundary_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hbottom htop hbottom' htop' hqBoundary

/--
[isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hbottom : rho <= p.2.1)
  (htop : p.2.1 + rho <= R)
  (hbottom' : rho <= p'.2.1)
  (htop' : p'.2.1 + rho <= R)
  (hqBoundary : isingLeapfrogBoxBoundary R q) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) p q - isingLeapfrogStoppedKernel R (rho * rho) p' q| <= 10296 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectedStart_boundary_diffusive_abs_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hhalf hbottom htop hbottom' htop' hqBoundary

/--
[sourceFailureOutputAt_horizontal_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureOutputAt_horizontal_diffusive_weight_le_eq
  {R level rho : Nat}
  {p q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level < R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingSourceFailureOutputAtFamily R (rho * rho) p q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureOutputAt_horizontal_diffusive_weight_le R level rho p q hstart hρ hleft hlevelR hqHorizontal

/--
[mirrorFailureOutputAt_horizontal_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorFailureOutputAt_horizontal_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingMirrorFailureOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorFailureOutputAt_horizontal_diffusive_weight_le R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal

/--
[sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hlevelR : level < R)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingStoppedCouplingSourceFailureAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 936 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.sourceFailureAt_horizontal_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hlevelR hright hhalf hqHorizontal

/--
[mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingStoppedCouplingMirrorFailureAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 1404 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorFailureAt_horizontal_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hhalf hqHorizontal

/--
[mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hright : level + rho <= R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingMirrorChoiceNoHitOutputAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.mirrorChoiceNoHitOutputAt_horizontal_diffusive_weight_le R level rho p p' q hstart hmirror hρ hright hqHorizontal

/--
[choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  Nat.card (IsingLeapfrogChoiceNoHitAtFamily R (rho * rho) p p' q (level : Int)) / (4 : Real) ^ (rho * rho) <= 936 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.choiceNoHitAt_horizontal_diffusive_weight_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hqHorizontal

/--
[isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf_eq
  {R level rho : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho <= level)
  (hright : level + rho <= R)
  (hhalf : R <= 2 * level)
  (hqHorizontal : q.1.1 = 0 ∨ q.1.1 = R) :
-- imply
  |isingLeapfrogStoppedKernel R (rho * rho) p q - isingLeapfrogStoppedKernel R (rho * rho) p' q| <= 3276 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectedStart_horizontalEndpoint_diffusive_abs_le_of_rightHalf R level rho p p' q hstart hmirror hρ hleft hright hhalf hqHorizontal


-- created on 2026-10-23

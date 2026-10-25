/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicLift.Part3
open scoped BigOperators


namespace StatMech.FrontierA

theorem triangularIntPeriodicPos_reduce
    {n : Nat} [NeZero n] (L : Nat) (direction : Fin n -> Fin 6)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep (direction k) =
      ((L : Int) * mx, (L : Int) * my)) (z : Int × Fin n) :
    triangularIntReduce L (triangularIntPeriodicPos direction z) =
      triangularIntReduce L (triangularIntPos direction z.2) := by
  rcases z with ⟨r, i⟩
  apply Prod.ext <;>
    simp [triangularIntPeriodicPos, triangularIntReduce,
      hdisplacement]

theorem triangularTorusCyclePeriodicPos_injective
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my))
    (hne : mx ≠ 0 ∨ my ≠ 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    Function.Injective (triangularIntPeriodicPos
      (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro z w hzw
  let direction : Fin p.darts.length -> Fin 6 :=
    fun k => (triangularTorusCycleNativeDart L p k).2
  have hred := congrArg (triangularIntReduce L) hzw
  rw [triangularIntPeriodicPos_reduce L direction mx my
      hdisplacement z,
    triangularIntPeriodicPos_reduce L direction mx my
      hdisplacement w] at hred
  have hsite : (triangularTorusCycleNativeDart L p z.2).1 =
      (triangularTorusCycleNativeDart L p w.2).1 := by
    rw [triangularTorusCycleNativeSite_eq_reduce_pos L p hp z.2,
      triangularTorusCycleNativeSite_eq_reduce_pos L p hp w.2,
      hred]
  have hindex : z.2 = w.2 :=
    triangularTorusCycleNativeSite_injective L p hp hsite
  rcases z with ⟨r, i⟩
  rcases w with ⟨s, j⟩
  dsimp only at hindex
  subst j
  apply Prod.ext
  · dsimp only
    have hL : (L : Int) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
        (Fact.out : 2 < L)))
    rcases hne with hx | hy
    · have heq : r * ((L : Int) * mx) = s * ((L : Int) * mx) := by
        have h := congrArg Prod.fst hzw
        dsimp [triangularIntPeriodicPos, direction] at h
        rw [hdisplacement] at h
        simpa using add_right_cancel h
      exact mul_right_cancel₀ (mul_ne_zero hL hx) heq
    · have heq : r * ((L : Int) * my) = s * ((L : Int) * my) := by
        have h := congrArg Prod.snd hzw
        dsimp [triangularIntPeriodicPos, direction] at h
        rw [hdisplacement] at h
        simpa using add_right_cancel h
      exact mul_right_cancel₀ (mul_ne_zero hL hy) heq
  · rfl

theorem triangularTorusCycleLiftPos_injective_of_closed
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2 = 0),
      Function.Injective (triangularIntPos
        (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro _
  exact triangularTorusCycleLiftPos_injective L p hp


theorem exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0),
      exists m : Int,
        (∑ k, triangularTorusTurnExponent
          (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k))
          (triangularTorusGraphDartDirection L
            (kwGraphCycleDartLoop p (k + 1)))) = 8 * (2 * m + 1) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro hclosed
  apply exists_triangularTorusTurnExponent_sum_eq_eight_mul_odd_of_closed
  · exact triangularTorus_cycleDirection_nonbacktracking L p hp
  · exact hclosed
  · simpa [SimpleGraph.Walk.length_darts] using hp.three_le_length
  · have hnclosed : ∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2 = 0 := by
      simpa only [triangularTorusCycleNativeDart_snd] using hclosed
    simpa only [triangularTorusCycleNativeDart_snd] using
      (triangularTorusCycleLiftPos_injective_of_closed L p hp hnclosed)


theorem triangularTorus_cyclePhaseProduct_eq_neg_one_of_closed
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (hclosed : ∑ k, triangularIntStep
        (triangularTorusGraphDartDirection L (kwGraphCycleDartLoop p k)) = 0),
      kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
        (kwGraphCycleDartLoop p) = -1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro hclosed
  obtain ⟨m, hm⟩ :=
    exists_triangularTorus_cycleTurnSum_eq_eight_mul_odd_of_closed L p hp hclosed
  exact triangularTorus_cyclePhaseProduct_eq_neg_one_of_odd_revolutions
    L rho hrho p hp m hm

end StatMech.FrontierA

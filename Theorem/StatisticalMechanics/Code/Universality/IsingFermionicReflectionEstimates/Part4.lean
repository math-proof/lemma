/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part2


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

theorem survivalExceptionalFirstHitFamily_code_injective
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    ∃ f : SurvivalExceptionalFirstHitFamily R start level walkLength target →
        {bits : List (Bool × Bool) // bits.length = walkLength},
      Function.Injective f := by
  exact ⟨fun w => firstHitFamilyCode w.1.1,
    fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact firstHitFamilyCode_injective h⟩


theorem natDist_survivingFirstHitFamily_le_exceptions
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int) :
    Nat.dist
        (Nat.card (SurvivingFirstHitFamily R start level walkLength target))
        (Nat.card (SurvivingFirstHitFamily R
          (reflectedEndpoint level start) level walkLength target)) ≤
      Nat.card (SurvivalExceptionalFirstHitFamily R start level
          walkLength target) +
        Nat.card (SurvivalExceptionalMirrorFamily R start level
          walkLength target) := by
  have hs := Nat.card_congr
    (survivingFirstHitFamilyPartitionEquiv R start level walkLength target)
  have hm := Nat.card_congr
    (survivingMirrorFamilyPartitionEquiv R start level walkLength target)
  rw [Nat.card_sum] at hs hm
  have hmatch := natCard_survivalMatchedFirstHitFamily_eq
    R start level walkLength target
  unfold Nat.dist
  omega


theorem survivalExceptional_reflected_exists_hit_right
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (hgap : level + 1 < R)
    (w : SurvivalExceptionalFirstHitFamily R start level walkLength target) :
    ∃ k, k < w.1.1.1.before.length ∧
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.1.1.1.reflectPrefix.steps.take k)).1 = R := by
  let split := w.1.1.1
  have hfirst := w.1.1.2.1
  have hvalid := w.1.1.2.2.1
  have hsurvive := w.1.2
  have hexception := w.2
  rcases survivalException_before_firstHit split hsurvive hexception with
    ⟨k, hkbefore, hklength, hout⟩
  have hsourceSide :
      (isingDiagonalWalkEndpoint start (split.before.take k)).1 < level :=
    hfirst.endpoint_take_fst_lt split hvalid (by omega) k hkbefore
  have hsourceAtK := hsurvive k (by
    rw [← reflectPrefix_length split]
    exact hklength)
  have hrefx := reflectPrefix_endpoint_take_fst_of_le_before
    split k hkbefore.le
  have hrefy := reflectPrefix_endpoint_take_snd_of_le_before
    split k hkbefore.le
  have hsourceSteps : split.steps.take k = split.before.take k := by
    unfold steps
    exact List.take_append_of_le_length hkbefore.le
  rw [hsourceSteps] at hsourceAtK hrefx hrefy
  have hrefRight : (R : Int) ≤
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (split.reflectPrefix.steps.take k)).1 := by
    unfold InOpenBox at hsourceAtK hout
    rcases hsourceAtK with ⟨hsx0, hsxR, hsy0, hsyR⟩
    have hrefPositive : 0 <
        (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
          (split.reflectPrefix.steps.take k)).1 := by
      rw [hrefx]
      omega
    have hrefY :
        0 < (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
              (split.reflectPrefix.steps.take k)).2 ∧
          (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
              (split.reflectPrefix.steps.take k)).2 < R := by
      rw [hrefy]
      exact ⟨hsy0, hsyR⟩
    omega
  have hrefValid := reflectPrefix_valid split hvalid
  have htakeValid : IsingDiagonalWalkStepsValid
      (split.reflectPrefix.steps.take k) := by
    intro d hd
    exact hrefValid d (List.mem_of_mem_take hd)
  have hrefStart : (reflectedEndpoint level start).1 < R := by
    unfold reflectedEndpoint
    dsimp
    omega
  rcases exists_prefix_fst_eq_of_lt_of_le
      (split.reflectPrefix.steps.take k) (reflectedEndpoint level start) R
      htakeValid hrefStart hrefRight with ⟨j, hj, heq⟩
  refine ⟨j, ?_, ?_⟩
  · have hjk : j ≤ k := by
      rw [List.length_take] at hj
      omega
    change j < split.before.length
    omega
  · have hjk : j ≤ k := by
      rw [List.length_take] at hj
      omega
    simpa [List.take_take, Nat.min_eq_left hjk] using heq


theorem survivalExceptionalMirror_reflected_exists_hit_left
    (R : Nat) (start : Int × Int) (level : Int) (walkLength : Nat)
    (target : Int × Int)
    (hstart : start.1 + 1 = level) (hlevel : 0 < level)
    (w : SurvivalExceptionalMirrorFamily R start level walkLength target) :
    ∃ k, k < w.1.1.1.before.length ∧
      (isingDiagonalWalkEndpoint start
        (w.1.1.1.reflectPrefix.steps.take k)).1 = 0 := by
  let split := w.1.1.1
  have hfirst := w.1.1.2.1
  have hvalid := w.1.1.2.2.1
  have hsurvive := w.1.2
  have hexception :
      ¬ StaysInOpenBox R start split.reflectPrefix.steps := by
    simpa [SurvivalExceptionalMirrorFamily, reflectPrefix, steps] using w.2
  have hexception' :
      ¬ StaysInOpenBox R (reflectedEndpoint level
        (reflectedEndpoint level start)) split.reflectPrefix.steps := by
    simpa using hexception
  rcases survivalException_before_firstHit split hsurvive hexception' with
    ⟨k, hkbefore, hklength, hout⟩
  have hmirrorStart : level < (reflectedEndpoint level start).1 := by
    unfold reflectedEndpoint
    dsimp
    omega
  have hsourceSide : level <
      (isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (split.before.take k)).1 :=
    hfirst.endpoint_take_fst_gt split hvalid hmirrorStart k hkbefore
  have hsourceAtK := hsurvive k (by
    rw [← reflectPrefix_length split]
    exact hklength)
  have hrefx := reflectPrefix_endpoint_take_fst_of_le_before
    split k hkbefore.le
  have hrefy := reflectPrefix_endpoint_take_snd_of_le_before
    split k hkbefore.le
  have hsourceSteps : split.steps.take k = split.before.take k := by
    unfold steps
    exact List.take_append_of_le_length hkbefore.le
  rw [hsourceSteps] at hsourceAtK hrefx hrefy
  have hrefLeftCanonical :
      (isingDiagonalWalkEndpoint (reflectedEndpoint level
          (reflectedEndpoint level start))
        (split.reflectPrefix.steps.take k)).1 ≤ 0 := by
    unfold InOpenBox at hsourceAtK hout
    rcases hsourceAtK with ⟨hsx0, hsxR, hsy0, hsyR⟩
    have hrefBelowR :
        (isingDiagonalWalkEndpoint (reflectedEndpoint level
          (reflectedEndpoint level start))
          (split.reflectPrefix.steps.take k)).1 < R := by
      rw [hrefx]
      omega
    have hrefY :
        0 < (isingDiagonalWalkEndpoint (reflectedEndpoint level
              (reflectedEndpoint level start))
              (split.reflectPrefix.steps.take k)).2 ∧
          (isingDiagonalWalkEndpoint (reflectedEndpoint level
              (reflectedEndpoint level start))
              (split.reflectPrefix.steps.take k)).2 < R := by
      rw [hrefy]
      exact ⟨hsy0, hsyR⟩
    omega
  have hrefLeft :
      (isingDiagonalWalkEndpoint start
        (split.reflectPrefix.steps.take k)).1 ≤ 0 := by
    simpa using hrefLeftCanonical
  have hrefValid := reflectPrefix_valid split hvalid
  have htakeValid : IsingDiagonalWalkStepsValid
      (split.reflectPrefix.steps.take k) := by
    intro d hd
    exact hrefValid d (List.mem_of_mem_take hd)
  by_cases hstartZero : start.1 = 0
  · refine ⟨0, ?_, ?_⟩
    · change 0 < split.before.length
      exact lt_of_le_of_lt (Nat.zero_le k) hkbefore
    simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement,
      hstartZero]
  · have hrefStart : 0 < start.1 := by omega
    rcases exists_prefix_fst_eq_of_ge_of_gt
        (split.reflectPrefix.steps.take k) start 0 htakeValid hrefStart
        hrefLeft with ⟨j, hj, heq⟩
    refine ⟨j, ?_, ?_⟩
    · have hjk : j ≤ k := by
        rw [List.length_take] at hj
        omega
      change j < split.before.length
      omega
    · have hjk : j ≤ k := by
        rw [List.length_take] at hj
        omega
      simpa [List.take_take, Nat.min_eq_left hjk] using heq

end IsingDiagonalWalkHitSplit
end StatMech.Universality

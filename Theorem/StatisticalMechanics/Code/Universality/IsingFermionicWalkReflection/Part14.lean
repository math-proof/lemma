/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part15


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


theorem reflectPrefix_endpoint_take_eq_of_before_length_le
    (w : IsingDiagonalWalkHitSplit start level) (k : Nat)
    (hk : w.before.length ≤ k) :
    isingDiagonalWalkEndpoint (reflectedEndpoint level start)
        (w.reflectPrefix.steps.take k) =
      isingDiagonalWalkEndpoint start (w.steps.take k) := by
  have hmap : (w.before.map reflectIncrement).length ≤ k := by
    simpa using hk
  simp only [steps, reflectPrefix, List.take_append]
  rw [List.take_of_length_le hk, List.take_of_length_le hmap]
  have hsub : k - (w.before.map reflectIncrement).length =
      k - w.before.length := by simp
  rw [hsub]
  apply Prod.ext
  · unfold isingDiagonalWalkEndpoint
    rw [displacement_append, displacement_append,
      displacement_reflectSuffix]
    unfold reflectedEndpoint
    have hw := w.hit
    dsimp at hw ⊢
    omega
  · unfold isingDiagonalWalkEndpoint
    rw [displacement_append, displacement_append,
      displacement_reflectSuffix]
    unfold reflectedEndpoint
    rfl


theorem survivalException_before_firstHit
    (w : IsingDiagonalWalkHitSplit start level)
    {R : Nat}
    (hs : StaysInOpenBox R start w.steps)
    (hr : ¬ StaysInOpenBox R (reflectedEndpoint level start)
      w.reflectPrefix.steps) :
    ∃ k, k < w.before.length ∧ k ≤ w.reflectPrefix.steps.length ∧
      ¬ InOpenBox R (isingDiagonalWalkEndpoint
        (reflectedEndpoint level start) (w.reflectPrefix.steps.take k)) := by
  classical
  unfold StaysInOpenBox at hr
  push Not at hr
  rcases hr with ⟨k, hk, hout⟩
  refine ⟨k, ?_, hk, hout⟩
  by_contra hnot
  have hbefore : w.before.length ≤ k := by omega
  have hk' : k ≤ w.steps.length := by
    rw [← reflectPrefix_length w]
    exact hk
  have hin := hs k hk'
  rw [reflectPrefix_endpoint_take_eq_of_before_length_le w k hbefore] at hout
  exact hout hin


theorem exists_prefix_fst_eq_of_lt_of_le
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstart : start.1 < level)
    (hend : level ≤ (isingDiagonalWalkEndpoint start path).1) :
    ∃ k, k ≤ path.length ∧
      (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
  induction path generalizing start with
  | nil =>
      simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement] at hend
      omega
  | cons d path ih =>
      have hd := hvalid d (by simp)
      let next := isingDiagonalWalkNext start d
      have hendpoint : isingDiagonalWalkEndpoint next path =
          isingDiagonalWalkEndpoint start (d :: path) := by
        unfold next isingDiagonalWalkNext isingDiagonalWalkEndpoint
          isingDiagonalWalkDisplacement
        apply Prod.ext <;> simp <;> ring
      by_cases hnext : next.1 = level
      · exact ⟨1, by simp, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement] using hnext⟩
      · have hnextlt : next.1 < level := by
          unfold next isingDiagonalWalkNext at hnext ⊢
          rcases hd.1 with hd | hd <;> omega
        have htailValid : IsingDiagonalWalkStepsValid path := by
          intro e he
          exact hvalid e (by simp [he])
        have htailEnd : level ≤ (isingDiagonalWalkEndpoint next path).1 := by
          rw [hendpoint]
          exact hend
        rcases ih next htailValid hnextlt htailEnd with ⟨k, hk, heq⟩
        exact ⟨k + 1, by simp; omega, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement, add_assoc] using heq⟩


theorem exists_prefix_fst_eq_of_ge_of_gt
    (path : List (Int × Int)) (start : Int × Int) (level : Int)
    (hvalid : IsingDiagonalWalkStepsValid path)
    (hstart : level < start.1)
    (hend : (isingDiagonalWalkEndpoint start path).1 ≤ level) :
    ∃ k, k ≤ path.length ∧
      (isingDiagonalWalkEndpoint start (path.take k)).1 = level := by
  induction path generalizing start with
  | nil =>
      simp [isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement] at hend
      omega
  | cons d path ih =>
      have hd := hvalid d (by simp)
      let next := isingDiagonalWalkNext start d
      have hendpoint : isingDiagonalWalkEndpoint next path =
          isingDiagonalWalkEndpoint start (d :: path) := by
        unfold next isingDiagonalWalkNext isingDiagonalWalkEndpoint
          isingDiagonalWalkDisplacement
        apply Prod.ext <;> simp <;> ring
      by_cases hnext : next.1 = level
      · exact ⟨1, by simp, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement] using hnext⟩
      · have hnextgt : level < next.1 := by
          unfold next isingDiagonalWalkNext at hnext ⊢
          rcases hd.1 with hd | hd <;> omega
        have htailValid : IsingDiagonalWalkStepsValid path := by
          intro e he
          exact hvalid e (by simp [he])
        have htailEnd : (isingDiagonalWalkEndpoint next path).1 ≤ level := by
          rw [hendpoint]
          exact hend
        rcases ih next htailValid hnextgt htailEnd with ⟨k, hk, heq⟩
        exact ⟨k + 1, by simp; omega, by
          simpa [next, isingDiagonalWalkEndpoint, isingDiagonalWalkNext,
            isingDiagonalWalkDisplacement, add_assoc] using heq⟩


theorem FirstHit.endpoint_take_fst_lt
    (w : IsingDiagonalWalkHitSplit start level)
    (hfirst : w.FirstHit) (hvalid : w.Valid)
    (hstart : start.1 < level) (k : Nat) (hk : k < w.before.length) :
    (isingDiagonalWalkEndpoint start (w.before.take k)).1 < level := by
  by_contra hnot
  have hend : level ≤
      (isingDiagonalWalkEndpoint start (w.before.take k)).1 := by omega
  have htakeValid : IsingDiagonalWalkStepsValid (w.before.take k) := by
    intro d hd
    apply hvalid d
    unfold steps
    exact List.mem_append.mpr (Or.inl (List.mem_of_mem_take hd))
  rcases exists_prefix_fst_eq_of_lt_of_le (w.before.take k) start level
      htakeValid hstart hend with ⟨j, hj, heq⟩
  have hjk : j ≤ k := by
    rw [List.length_take] at hj
    omega
  have hjbefore : j < w.before.length := by omega
  have hno := hfirst j hjbefore
  apply hno
  simpa [List.take_take, Nat.min_eq_left hjk] using heq


theorem FirstHit.endpoint_take_fst_gt
    (w : IsingDiagonalWalkHitSplit start level)
    (hfirst : w.FirstHit) (hvalid : w.Valid)
    (hstart : level < start.1) (k : Nat) (hk : k < w.before.length) :
    level < (isingDiagonalWalkEndpoint start (w.before.take k)).1 := by
  by_contra hnot
  have hend :
      (isingDiagonalWalkEndpoint start (w.before.take k)).1 ≤ level := by
    omega
  have htakeValid : IsingDiagonalWalkStepsValid (w.before.take k) := by
    intro d hd
    apply hvalid d
    unfold steps
    exact List.mem_append.mpr (Or.inl (List.mem_of_mem_take hd))
  rcases exists_prefix_fst_eq_of_ge_of_gt (w.before.take k) start level
      htakeValid hstart hend with ⟨j, hj, heq⟩
  have hjk : j ≤ k := by
    rw [List.length_take] at hj
    omega
  have hjbefore : j < w.before.length := by omega
  have hno := hfirst j hjbefore
  apply hno
  simpa [List.take_take, Nat.min_eq_left hjk] using heq


end IsingDiagonalWalkHitSplit
end StatMech.Universality

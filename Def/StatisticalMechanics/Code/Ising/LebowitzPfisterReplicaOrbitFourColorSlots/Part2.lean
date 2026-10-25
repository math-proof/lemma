/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaCurrentEdgeOrbitCoordEquiv
    (G : SimpleGraph V) (sites : I -> V) :
    (lpReplicaCurrentGraph G sites).edgeFinset ≃
      ↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
        (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
          ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) where
  toFun e := by
    classical
    by_cases hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites
    · exact Sum.inl ⟨e, hfixed⟩
    · by_cases hstrict : e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites
      · exact Sum.inr (Sum.inl ⟨e, hstrict⟩)
      · exact Sum.inr (Sum.inr
          ⟨lpReplicaCurrentEdgeReflect G sites e,
            lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem
              G sites e hfixed hstrict⟩)
  invFun
    | Sum.inl e => e.1
    | Sum.inr (Sum.inl e) => e.1
    | Sum.inr (Sum.inr e) => lpReplicaCurrentEdgeReflect G sites e.1
  left_inv := by
    classical
    intro e
    by_cases hfixed : e ∈ lpReplicaCurrentEdgeOrbitFixed G sites
    · simp [hfixed]
    · by_cases hstrict : e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites
      · simp [hfixed, hstrict]
      · simp only [hfixed, hstrict, ↓reduceDIte]
        exact lpReplicaCurrentEdgeReflect_involutive G sites e
  right_inv := by
    classical
    intro x
    rcases x with fixed | strict
    · simp [fixed.2]
    · rcases strict with rep | reflected
      · have hnotFixed : rep.1 ∉
            lpReplicaCurrentEdgeOrbitFixed G sites := by
          intro hfixed
          exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites rep.1).1
            rep.2).2 ((mem_lpReplicaCurrentEdgeOrbitFixed G sites rep.1).1
              hfixed)
        simp [hnotFixed, rep.2]
      · have hnotFixed : lpReplicaCurrentEdgeReflect G sites reflected.1 ∉
            lpReplicaCurrentEdgeOrbitFixed G sites := by
          intro hfixed
          have heq := (mem_lpReplicaCurrentEdgeOrbitFixed G sites _).1 hfixed
          have heq' : lpReplicaCurrentEdgeReflect G sites reflected.1 =
              reflected.1 := by
            rw [lpReplicaCurrentEdgeReflect_involutive] at heq
            exact heq
          exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites reflected.1).1
            reflected.2).2 heq'.symm
        have hnotStrict : lpReplicaCurrentEdgeReflect G sites reflected.1 ∉
            lpReplicaCurrentEdgeOrbitStrictReps G sites := by
          intro hstrict
          have hrep := (mem_lpReplicaCurrentEdgeOrbitStrictReps
            G sites reflected.1).1 reflected.2
          have href := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites
            (lpReplicaCurrentEdgeReflect G sites reflected.1)).1 hstrict
          exact hrep.2
            (lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
              G sites reflected.1 hrep.1 (by
                simpa only [lpReplicaCurrentEdgeReflect_involutive]
                  using href.1))
        simp only [hnotFixed, hnotStrict, ↓reduceDIte]
        apply congrArg Sum.inr
        apply congrArg Sum.inr
        apply Subtype.ext
        exact lpReplicaCurrentEdgeReflect_involutive G sites reflected.1

end
end StatMech.Ising

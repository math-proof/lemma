/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitCommonSlotOrderKey_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective (lpReplicaOrbitCommonSlotOrderKey G sites q) := by
  intro x y h
  rcases x with ⟨e, k⟩ | ⟨e, k⟩ <;>
    rcases y with ⟨f, l⟩ | ⟨f, l⟩
  · change (0, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (0, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    have h' := congrArg (fun z : Nat × Lex (Nat × Nat) => z.2) h
    change ((lpReplicaCurrentEdgeRank G sites e.1 : Nat), (k : Nat)) =
      ((lpReplicaCurrentEdgeRank G sites f.1 : Nat), (l : Nat)) at h'
    have hrank : lpReplicaCurrentEdgeRank G sites e.1 =
        lpReplicaCurrentEdgeRank G sites f.1 := Fin.ext
          (congrArg (fun z : Nat × Nat => z.1) h')
    have hef : e.1 = f.1 :=
      lpReplicaCurrentEdgeRank_injective G sites hrank
    have he : e = f := Subtype.ext hef
    subst f
    have hkl : k = l := Fin.ext
      (congrArg (fun z : Nat × Nat => z.2) h')
    subst l
    rfl
  · change (0, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (1, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    exact (Nat.zero_ne_one (congrArg
      (fun z : Nat × Lex (Nat × Nat) => z.1) h)).elim
  · change (1, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (0, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    exact (Nat.one_ne_zero (congrArg
      (fun z : Nat × Lex (Nat × Nat) => z.1) h)).elim
  · change (1, toLex ((lpReplicaCurrentEdgeRank G sites e.1 : Nat),
        (k : Nat))) =
      (1, toLex ((lpReplicaCurrentEdgeRank G sites f.1 : Nat),
        (l : Nat))) at h
    have h' := congrArg (fun z : Nat × Lex (Nat × Nat) => z.2) h
    change ((lpReplicaCurrentEdgeRank G sites e.1 : Nat), (k : Nat)) =
      ((lpReplicaCurrentEdgeRank G sites f.1 : Nat), (l : Nat)) at h'
    have hrank : lpReplicaCurrentEdgeRank G sites e.1 =
        lpReplicaCurrentEdgeRank G sites f.1 := Fin.ext
          (congrArg (fun z : Nat × Nat => z.1) h')
    have hef : e.1 = f.1 :=
      lpReplicaCurrentEdgeRank_injective G sites hrank
    have he : e = f := Subtype.ext hef
    subst f
    have hkl : k = l := Fin.ext
      (congrArg (fun z : Nat × Nat => z.2) h')
    subst l
    rfl


end
end StatMech.Ising

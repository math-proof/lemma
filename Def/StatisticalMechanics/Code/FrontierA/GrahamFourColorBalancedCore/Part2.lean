/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Instance.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


noncomputable def boundarySectorEquivCycle (ends : ι → Sym2 W) (S X : Finset ι)
    (b : Finset W) (hXsub : X ⊆ S) (hXsrc : Sharpness.RandomCurrent.sources ends X = b) :
    boundarySector ends S b ≃ boundarySector ends S ∅ := by
  classical
  let shift : Finset ι → Finset ι := fun T => T ∆ X
  refine
    { toFun := fun T => ⟨shift T.1, ?_⟩
      invFun := fun T => ⟨shift T.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro i hi
      rw [Finset.mem_symmDiff] at hi
      exact hi.elim (fun h => T.2.1 h.1) (fun h => hXsub h.1)
    · dsimp only [shift]
      rw [Sharpness.RandomCurrent.sources_symmDiff, T.2.2, hXsrc, symmDiff_self]
      rfl
  · constructor
    · intro i hi
      rw [Finset.mem_symmDiff] at hi
      exact hi.elim (fun h => T.2.1 h.1) (fun h => hXsub h.1)
    · dsimp only [shift]
      rw [Sharpness.RandomCurrent.sources_symmDiff, T.2.2, hXsrc]
      simp
  · intro T
    apply Subtype.ext
    simp [shift]
  · intro T
    apply Subtype.ext
    simp [shift]


end FourColor
end GrahamGHS
end StatMech

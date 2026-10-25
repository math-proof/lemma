/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Mathlib.Algebra.Lie.Semisimple.Defs
import Structure.v1.Atlas.LieGroups.code.GKModuleDefs


noncomputable section

open scoped ComplexOrder

namespace GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

def lieIterate (Xs : List 𝔤) (v : V) : V :=
  Xs.foldr (fun X acc => ⁅X, acc⁆) v

def IsHarishChandraModule (M : GKModule 𝔤 K 𝔨 Ad V) : Prop :=
  M.IsAdmissible ∧
  ∃ (S : Finset V), ∀ v : V,
    v ∈ Submodule.span ℂ
      (⋃ (s : V) (_ : s ∈ S) (Xs : List 𝔤),
        ({lieIterate Xs s} : Set V))

end GKModule
end

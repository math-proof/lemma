/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HighestWeightModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Mathlib.Algebra.Lie.Sl2
import Def.v1.Atlas.LieGroups.code.HighestWeightModules


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

structure ChevalleyData (Δ : TriangularDecomposition R 𝔤) where
  rank : ℕ
  simpleCoroot : Fin rank → Δ.𝔥
  posGen : Fin rank → 𝔤
  negGen : Fin rank → 𝔤
  posGen_mem : ∀ i, posGen i ∈ Δ.𝔫_pos
  negGen_mem : ∀ i, negGen i ∈ Δ.𝔫_neg
  bracket_ef : ∀ i, ⁅posGen i, negGen i⁆ = (simpleCoroot i : 𝔤)
  bracket_he : ∀ i, ⁅(simpleCoroot i : 𝔤), posGen i⁆ = posGen i + posGen i
  bracket_hf : ∀ i, ⁅(simpleCoroot i : 𝔤), negGen i⁆ = -(negGen i + negGen i)

end

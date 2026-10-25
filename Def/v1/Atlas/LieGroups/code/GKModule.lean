/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Dimension.Finite


noncomputable section

def Representation.IsLocallyFinite {K V : Type*} [Group K]
    [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ K V) : Prop :=
  ∀ v : V, FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun k : K => (σ k) v)) : Submodule ℂ V)

end

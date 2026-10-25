/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Admissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import Lemma.Complex.IsKFinite0
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Real.IsSmoothVector0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Def.v1.Atlas.LieGroups.code.SmoothVectors
import Theorem.v1.Atlas.LieGroups.code.SmoothVectorsProps
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Theorem.v1.Atlas.LieGroups.code.Admissible
universe uF


noncomputable section

open scoped ComplexOrder Manifold

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

noncomputable def schurProjector
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) : F →L[ℂ] F :=
  (schurProjector_exists_raw π K σ hirr).choose

end ContinuousRep
end

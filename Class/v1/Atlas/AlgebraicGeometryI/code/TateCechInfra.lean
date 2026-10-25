/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TateCechInfra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityTate.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityTate
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SerreDualityAnnihilator
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator
import Def.v1.Atlas.AlgebraicGeometryI.code.TateCechInfra


section TateVectorSpaceDef

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A Tate vector space over `k` (Def 46, Lec 25): a topological `k`-vector
space whose neighborhood basis of zero consists of pairwise commensurable
linear subspaces. -/
class IsTateVectorSpace (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [TopologicalSpace V] : Prop where
  exists_nhds_basis : ∃ (ι : Type*) (W : ι → Submodule k V),
    (nhds (0 : V)).HasBasis (fun _ : ι => True) (fun i => ↑(W i)) ∧
    ∀ i j, IsCommensurable (W i) (W j)

end TateVectorSpaceDef

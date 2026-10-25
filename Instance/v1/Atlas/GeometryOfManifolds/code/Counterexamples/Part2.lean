/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Class.v1.Atlas.GeometryOfManifolds.code.Counterexamples
set_option autoImplicit false

open DifferentialFormSpace


/-- The free abelian group $\mathbb{Z}$ has rank $1$. -/
instance freeAbelianRank_Z : FreeAbelianRank (Multiplicative ℤ) where
  rank := 1

/-- The rank of a product of free abelian groups is the sum of the ranks. -/
instance freeAbelianRank_prod {A B : Type*} [CommGroup A] [CommGroup B]
    [FreeAbelianRank A] [FreeAbelianRank B] :
    FreeAbelianRank (A × B) where
  rank := FreeAbelianRank.rank (G := A) + FreeAbelianRank.rank (G := B)


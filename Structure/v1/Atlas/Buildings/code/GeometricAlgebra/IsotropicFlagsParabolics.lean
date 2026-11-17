/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/IsotropicFlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
public import Theorem.Submodule.OfEq.eq.M.of.Eq
public import Lemma.Fin.Eq.of.Ne_0.All_Eq
public import Lemma.Submodule.Any_EqMapToLinearMap.of.FinrankK
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2
public import Instance.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.IsotropicFlagsParabolics


public section

namespace Garrett

variable {k : Type*} [Field k] [DecidableEq k] [NeZero (2 : k)]
  {V : Type*} [AddCommGroup V] [Module k V]


/-- An isotropic flag in a formed space `(V, B)` is a strictly increasing chain
of totally isotropic subspaces. -/
structure IsotropicFlag (B : LinearMap.BilinForm k V) where
  len : ℕ
  spaces : Fin len → Submodule k V
  strictMono : StrictMono spaces
  isotropic : ∀ i, IsTotallyIsotropic B (spaces i)

end Garrett

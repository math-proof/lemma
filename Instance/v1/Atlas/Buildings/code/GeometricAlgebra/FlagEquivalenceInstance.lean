/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part3
public import Theorem.Fin.EqLinearEquivToGLV_GlvToLinearEquiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance
@[expose] public section

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The `FlagEquivalenceProperty` instance: over any field, on a
finite-dimensional vector space, flags of the same type are `GL(V)`-equivalent. -/
instance instFlagEquivalenceProperty [FiniteDimensional k V] :
    FlagEquivalenceProperty k V where
  equiv_linear := flag_equiv_of_sameType k V

end GeometricAlgebra

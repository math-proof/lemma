/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagEquivalenceInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part3
import Lemma.Fin.EqLinearEquivToGLV_GlvToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagEquivalenceInstance


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The `FlagEquivalenceProperty` instance: over any field, on a
finite-dimensional vector space, flags of the same type are `GL(V)`-equivalent. -/
instance instFlagEquivalenceProperty [FiniteDimensional k V] :
    FlagEquivalenceProperty k V where
  equiv_linear := flag_equiv_of_sameType k V

end GeometricAlgebra

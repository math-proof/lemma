/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

def IsNilpotentElement (x : L) : Prop :=
  IsNilpotent (LieAlgebra.ad R L x)

def NilpotentCone : Set L :=
  {x : L | IsNilpotentElement R L x}

end LieAlgebra
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs
import Abbrev.v1.Atlas.LieGroups.code.VermaModules


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def vermaIdeal (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    RingCon (UniversalEnvelopingAlgebra R 𝔤) :=
  ringConGen (fun a b =>
    (∃ h : Δ.𝔥, a = UniversalEnvelopingAlgebra.ι R (h : 𝔤) ∧
               b = algebraMap R (UniversalEnvelopingAlgebra R 𝔤) (wt h)) ∨
    (∃ e : Δ.𝔫_pos, a = UniversalEnvelopingAlgebra.ι R (e : 𝔤) ∧ b = 0))

def VermaModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Type _ :=
  (vermaIdeal Δ wt).Quotient

end TriangularDecomposition
end

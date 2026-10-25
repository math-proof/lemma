/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Order
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Constructions
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec2ProjectiveSpace
set_option maxHeartbeats 800000

open scoped LinearAlgebra.Projectivization


noncomputable section

namespace Formalization

/-- The quotient map `A^{n+1} \ {0} → P^n` sending a nonzero vector to its projective class
(Lecture 2, Definition 4). -/
def ProjectiveSpace.π (k : Type*) [Field k] (n : ℕ) :
    PuncturedAffineSpace k n → ProjectiveSpace k n :=
  Projectivization.mk' k

variable {k : Type*} [Field k] {n : ℕ}

/-- The vanishing locus in `A^{n+1}` of a set of polynomials: points where every polynomial in
`S` evaluates to zero. -/
def AffineSpace.zeroLocus (S : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (Fin (n + 1) → k) :=
  { x | ∀ p ∈ S, MvPolynomial.eval x p = 0 }

/-- The set of all products `f * g` with `f ∈ S` and `g ∈ T`, used in showing the union of two
zero loci is itself a zero locus. -/
def AffineSpace.mulPairs (S T : Set (MvPolynomial (Fin (n + 1)) k)) :
    Set (MvPolynomial (Fin (n + 1)) k) :=
  { p | ∃ f ∈ S, ∃ g ∈ T, f * g = p }

end Formalization
end

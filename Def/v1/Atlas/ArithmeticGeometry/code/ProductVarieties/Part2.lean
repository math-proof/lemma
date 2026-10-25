/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProductVarieties
variable (k : Type*) [Field k]


/-- Evaluation at a point $P \in V$ descends to a ring homomorphism
$\overline{k}[V] \to \overline{k}$ from the coordinate ring. -/
noncomputable def evalOnCoordinateRingBar
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    AffineCoordinateRingBar V →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet V) (MvPolynomial.eval P)
    (idealOfAlgebraicSet_le_ker_eval V P hP)

/-- The maximal ideal $\mathfrak{m}_P \subseteq \overline{k}[V]$ associated to a point
$P \in V$, defined as the kernel of evaluation at $P$. -/
noncomputable def maximalIdealOfPoint
    (V : Set (AffineSpace_k k n))
    (P : AffineSpace_k k n) (hP : P ∈ V) :
    Ideal (AffineCoordinateRingBar V) :=
  RingHom.ker (evalOnCoordinateRingBar V P hP)

/-- The product projective space $\mathbb{P}^m \times \mathbb{P}^n$ over $k$ as a Cartesian
product of projective spaces. -/
def ProductProjectiveSpace (k : Type*) [Field k] (m n : ℕ) : Type _ :=
  ProjectiveSpace_k k m × ProjectiveSpace_k k n


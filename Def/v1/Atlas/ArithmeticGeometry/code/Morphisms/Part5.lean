/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Theorem.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part3


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- A ring homomorphism between coordinate rings over $\bar k$ is *$\bar k$-algebra
preserving* if it fixes the scalar subring, i.e. sends $\bar r \in \bar k[Y]$ to
$\bar r \in \bar k[X]$ for every $r \in \bar k$. -/
def IsAlgHomBar {m n : ℕ}
    {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
    (θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X) : Prop :=
  ∀ r : AlgebraicClosure k,
    θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
    Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r)

end

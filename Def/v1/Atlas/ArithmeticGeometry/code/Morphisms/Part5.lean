module
public import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
public import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
public import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Theorem.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

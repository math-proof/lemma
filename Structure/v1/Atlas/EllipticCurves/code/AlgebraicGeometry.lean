/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Def.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part3
open MvPolynomial Set


public noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- A representation of a homogeneous rational function on the projective curve
defined by `f`: a numerator and denominator, both homogeneous of the same
degree, with the denominator not in the ideal `(f)`. -/
structure HomogeneousRationalFunction (k : Type*) [CommRing k]
    (f : MvPolynomial (Fin 3) k) where
  num : MvPolynomial (Fin 3) k
  den : MvPolynomial (Fin 3) k
  deg : ℕ
  num_homogeneous : num.IsHomogeneous deg
  den_homogeneous : den.IsHomogeneous deg
  den_not_in_ideal : den ∉ Ideal.span ({f} : Set (MvPolynomial (Fin 3) k))

end

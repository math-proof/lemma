/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/AlgebraicGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Def.v1.Atlas.EllipticCurves.code.AlgebraicGeometry.Part3
open MvPolynomial Set


noncomputable section

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

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
import Instance.v1.Atlas.EllipticCurves.code.AlgebraicGeometry
open MvPolynomial Set


noncomputable section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

variable {σ : Type*}

/-- An alternative model of the function field of `Z(f)` as the fraction
field of the quotient ring `k[x, y, z] / (f)`. -/
abbrev functionFieldFrac (k : Type*) [Field k]
    (f : MvPolynomial (Fin 3) k) [Fact (Irreducible f)] :=
  FractionRing (MvPolynomial (Fin 3) k ⧸ Ideal.span ({f} : Set (MvPolynomial (Fin 3) k)))


/-- The affine function field of an affine algebraic set `V`: the fraction
field of its coordinate ring `K[V]`. -/
abbrev affineFunctionField (K : Type*) [Field K]
    (σ : Type*) (V : Set (σ → K)) :=
  FractionRing (coordinateRing K σ V)

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Abbrev.v1.Atlas.ArithmeticGeometry.code.AffineVarieties
variable (k : Type*) [Field k]


/-- The set of $L$-rational points in affine $n$-space: tuples all of whose coordinates lie
in the intermediate field $L \subseteq \overline{k}$. -/
def LRationalPoints (n : ℕ) (L : IntermediateField k (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  {P | ∀ i, P i ∈ L}



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
import Instance.v1.Atlas.ArithmeticGeometry.code.AffineVarieties
variable (k : Type*) [Field k]


section GaloisCharacterization

variable [PerfectField k]

/-- The set of points in $\overline{k}^n$ fixed by every element of the Galois group fixing
the intermediate field $L$ (the Galois-theoretic characterization of $L$-rational points). -/
def galoisFixedPoints (n : ℕ) (L : IntermediateField k (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  {P | ∀ (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k),
    σ ∈ L.fixingSubgroup → (fun i => σ (P i)) = P}


end GaloisCharacterization

/-- The algebraic set $V(S)$ in $\overline{k}^n$ cut out by a set $S$ of polynomials over
$\overline{k}$, i.e. the common zero locus. -/
def AlgebraicSet (n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (AffineSpace_k k n) :=
  {P | ∀ f ∈ S, MvPolynomial.eval P f = 0}


/-- The $L$-rational points of the algebraic set $V(S)$: zeros of $S$ with all coordinates
in the intermediate field $L$. -/
def AlgebraicSetLRational (n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k)))
    (L : IntermediateField k (AlgebraicClosure k)) : Set (AffineSpace_k k n) :=
  AlgebraicSet k n S ∩ LRationalPoints k n L


/-- The hypersurface $V(f) = \{P : f(P) = 0\}$ cut out by a single polynomial $f$. -/
def AlgebraicSetSingleton (n : ℕ) (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    Set (AffineSpace_k k n) :=
  AlgebraicSet k n {f}



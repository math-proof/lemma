/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Abbrev.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part4
open scoped LinearAlgebra.Projectivization


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveVarietyDef

variable {n : ℕ} (k : Type*) [Field k]

/-- An affine algebraic set $V$ has dimension $d$ if the Krull dimension of
its coordinate ring equals $d$. -/
def HasAffineDimension (N : ℕ) (V : Set (AffinePoint k N)) (d : ℕ) : Prop :=
  Order.krullDim (PrimeSpectrum (coordinateRing' k N V)) = ↑(d : ℕ∞)

/-- Jacobian matrix at the point $P$: the $m \times N$ matrix whose
$(i, j)$-entry is $\partial f_i / \partial X_j \,(P)$. -/
def jacobianMatrix (N m : ℕ) (f : Fin m → MvPolynomial (Fin N) (AlgebraicClosure k))
    (P : AffinePoint k N) : Matrix (Fin m) (Fin N) (AlgebraicClosure k) :=
  fun i j => MvPolynomial.eval P (MvPolynomial.pderiv j (f i))

/-- Singular locus of the system $f$: those zeros of $f$ at which the rank of
the Jacobian is strictly less than the codimension threshold $r$. -/
def singularLocus' (N m r : ℕ) (f : Fin m → MvPolynomial (Fin N) (AlgebraicClosure k)) :
    Set (AffinePoint k N) :=
  { P | P ∈ zeroLocus k N (Set.range f) ∧ (jacobianMatrix k N m f P).rank < r }

/-- Base change of an affine variety $V \subseteq k^n$ to $\overline{k}^n$ via
the canonical algebra map $k \hookrightarrow \overline{k}$. -/
def affinePartBaseChange (V : Set (Fin n → k)) : Set (AffinePoint k n) :=
  Set.image (fun (p : Fin n → k) (i : Fin n) => algebraMap k (AlgebraicClosure k) (p i)) V


/-- Coefficient lift $k[X_1, \ldots, X_N] \to \overline{k}[X_1, \ldots, X_N]$
via the canonical algebra map. -/
def liftToAlgClosure (N : ℕ) :
    MvPolynomial (Fin N) k →+* MvPolynomial (Fin N) (AlgebraicClosure k) :=
  MvPolynomial.map (algebraMap k (AlgebraicClosure k))

/-- Generators of the affine piece in chart $U_i$ over $\overline{k}$:
dehomogenize each $f_j$ at index $i$, then lift coefficients to
$\overline{k}$. -/
def affinePartGenerators {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (i : Fin (n + 1)) : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k) :=
  fun j => liftToAlgClosure k n (AffineParts.dehomogenize k i (f j))

/-- Zero locus over $\overline{k}$ of the affine generators in chart $U_i$. -/
def affinePartZeroLocusAlgClosed {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (i : Fin (n + 1)) : Set (AffinePoint k n) :=
  zeroLocus k n (Set.range (affinePartGenerators k f i))

/-- Projective dimension of the variety cut out by $f$: every affine chart has
dimension $\le d$, and at least one chart realizes dimension $d$. -/
def HasProjectiveDimension {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k)
    (d : ℕ) : Prop :=

  (∀ (i : Fin (n + 1)) (d_i : ℕ),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d_i →
    d_i ≤ d) ∧

  (∃ (i : Fin (n + 1)),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d)

/-- An affine piece of dimension $d$ is *smooth* when its singular locus (rank
$< n - d$) is empty. -/
def IsAffinePartSmooth {m : ℕ} (g : Fin m → MvPolynomial (Fin n) (AlgebraicClosure k))
    (d : ℕ) : Prop :=
  singularLocus' k n m (n - d) g = ∅

/-- A projective variety is *smooth* if each of its affine charts of
dimension $d_i$ is smooth. -/
def IsProjectiveSmooth {m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ (i : Fin (n + 1)) (d_i : ℕ),
    HasAffineDimension k n (affinePartZeroLocusAlgClosed k f i) d_i →
    IsAffinePartSmooth k (affinePartGenerators k f i) d_i

end ProjectiveVarietyDef
end

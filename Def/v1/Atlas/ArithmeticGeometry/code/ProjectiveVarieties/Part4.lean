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
import Abbrev.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part3
open scoped LinearAlgebra.Projectivization


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveVarietyDef

variable {n : ℕ} (k : Type*) [Field k]

/-- Affine zero locus of a set $S$ over $\overline{k}$: the common
$\overline{k}$-vanishing set of $S \subseteq \overline{k}[X_1, \ldots, X_N]$. -/
def zeroLocus (N : ℕ) (S : Set (MvPolynomial (Fin N) (AlgebraicClosure k))) :
    Set (AffinePoint k N) :=
  {P | ∀ f ∈ S, MvPolynomial.eval P f = 0}

/-- Vanishing ideal of a set $V \subseteq \overline{k}^N$: the ideal of
polynomials over $\overline{k}$ that vanish on every point of $V$. -/
def vanishingIdeal' (N : ℕ) (V : Set (AffinePoint k N)) :
    Ideal (MvPolynomial (Fin N) (AlgebraicClosure k)) :=
  { carrier := {f | ∀ P ∈ V, MvPolynomial.eval P f = 0}
    add_mem' := fun {a b} ha hb P hP => by simp [ha P hP, hb P hP]
    zero_mem' := fun P _ => by simp
    smul_mem' := fun c f hf P hP => by simp [hf P hP] }

end ProjectiveVarietyDef
end

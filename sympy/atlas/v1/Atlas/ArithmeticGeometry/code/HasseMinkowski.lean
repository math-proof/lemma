/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowski.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Rat.Star
import Mathlib.Data.Nat.Squarefree
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HasseMinkowskiProof
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.SquareClassApprox
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.SquareClassApprox

open scoped Classical

noncomputable section

namespace QuadraticMap

/-- A quadratic form $Q$ on a module $M$ is **isotropic** if it has a nontrivial zero, i.e., there
exists $v \neq 0$ with $Q(v) = 0$. -/
def IsIsotropic {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (Q : QuadraticForm R M) : Prop :=
  ∃ v : M, v ≠ 0 ∧ Q v = 0


end QuadraticMap

/-- The diagonal quadratic form $\sum_i a_i x_i^2$ with rational coefficients
$a_0, \dots, a_{n-1} \in \mathbb{Q}$. -/
def diagQuadForm (n : ℕ) (a : Fin n → ℚ) : QuadraticForm ℚ (Fin n → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ a

/-- The diagonal quadratic form $\sum_i a_i x_i^2$ with rational coefficients $a_i$, viewed as a
quadratic form over a $\mathbb{Q}$-algebra $F$. -/
def diagQuadFormOver (F : Type*) [Field F] [Algebra ℚ F]
    (n : ℕ) (a : Fin n → ℚ) : QuadraticForm F (Fin n → F) :=
  QuadraticMap.weightedSumSquares F (fun i => algebraMap ℚ F (a i))

/-- **Hasse-Minkowski for quaternary forms ($n = 4$).** A quaternary diagonal form is isotropic
over $\mathbb{Q}$ iff it is isotropic over $\mathbb{R}$ and over every $\mathbb{Q}_p$. -/
def replacedForm {m : ℕ} (a : Fin (m + 5) → ℚ) (t : ℚ) : Fin (m + 4) → ℚ :=
  fun i => if i.val = 0 then t else a ⟨i.val + 1, by omega⟩

/-- The "subform" coefficients obtained by dropping the first two entries
$(a_2, a_3, \dots, a_{m+4})$. -/
def subFormCoeffs {m : ℕ} (a : Fin (m + 5) → ℚ) : Fin (m + 3) → ℚ :=
  fun j => a ⟨j.val + 2, by omega⟩

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem11_1
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertProductFormula
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.QuadraticForm.Radical

open scoped Classical

/-- The ternary form $a x^2 + b y^2 + c z^2$ with unit coefficients $a, b, c \in F^\times$
**represents zero** if there is a nontrivial solution $(x, y, z) \neq (0, 0, 0)$ with
$a x^2 + b y^2 + c z^2 = 0$. -/
def TernaryForm.RepresentsZero (F : Type*) [Field F] (a b c : Fˣ) : Prop :=
  ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
    (a : F) * x ^ 2 + (b : F) * y ^ 2 + (c : F) * z ^ 2 = 0

/-- The binary form $a x^2 + b y^2$ with unit coefficients $a, b \in F^\times$ **represents**
$t \in F$ if there exist $x, y \in F$ such that $a x^2 + b y^2 = t$. -/
def BinaryForm.Represents (F : Type*) [Field F] (a b : Fˣ) (t : F) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = t

/-- The canonical map sending a rational unit $a \in \mathbb{Q}^\times$ to a real unit
$a \in \mathbb{R}^\times$. -/
def Corollary115.ratToRealUnits (a : ℚˣ) : ℝˣ :=
  Units.mk0 ((a : ℚ) : ℝ) (by exact_mod_cast a.ne_zero)

/-- The canonical map sending a rational unit $a \in \mathbb{Q}^\times$ to a $p$-adic unit
$a \in \mathbb{Q}_p^\times$. -/
def Corollary115.ratToQpUnits (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ) : ℚ_[p]ˣ :=
  Units.mk0 ((a : ℚ) : ℚ_[p]) (by exact_mod_cast a.ne_zero)

/-- The Hilbert symbol at the archimedean place: $(a, b)_\infty$ equals the real Hilbert
symbol of $a, b$ regarded as units of $\mathbb{R}^\times$. -/
def Corollary115.hilbertAtInfty (a b : ℚˣ) : ℤ :=
  realHilbertSymbol (Corollary115.ratToRealUnits a) (Corollary115.ratToRealUnits b)

/-- The Hilbert symbol at the finite place $p$: $(a, b)_p$ is the $p$-adic Hilbert symbol
of $a, b$ regarded as units of $\mathbb{Q}_p^\times$. -/
def Corollary115.hilbertAtPrime (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) : ℤ :=
  padicHilbertSymbol p (Corollary115.ratToQpUnits p a) (Corollary115.ratToQpUnits p b)

/-- The **global Hilbert product** $\prod_v (a, b)_v$, taken over all places of $\mathbb{Q}$:
the archimedean place $\infty$ and all finite primes $p$. -/
def Corollary115.globalHilbertProduct (a b : ℚˣ) : ℤ :=
  Corollary115.hilbertAtInfty a b *
  ∏ᶠ (p : Nat.Primes),
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b

/-- The set of places of $\mathbb{Q}$: either the archimedean (infinite) place $\infty$
or a finite place $p$ given by a prime. -/
inductive Place where
  | infty : Place
  | finite : Nat.Primes → Place
  deriving DecidableEq

/-- The Hilbert symbol $(a, b)_v$ at the place $v$ of $\mathbb{Q}$, taking values in
$\{1, -1\}$. -/
def hilbertAt (v : Place) (a b : ℚˣ) : ℤ :=
  match v with
  | Place.infty => Corollary115.hilbertAtInfty a b
  | Place.finite p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b

/-- The element $2 \in \mathbb{Q}$ is invertible (needed for converting between quadratic forms
and their associated symmetric matrices over $\mathbb{Q}$). -/
noncomputable instance invertibleTwoQ : Invertible (2 : ℚ) :=
  invertibleOfNonzero (by norm_num : (2 : ℚ) ≠ 0)

/-- A symmetric matrix $M$ over $\mathbb{Q}$ defines a quadratic form $x \mapsto x^T M x$, and
**represents zero $p$-adically** if there exists a nonzero vector $x \in \mathbb{Q}_p^n$ with
$x^T M x = 0$. -/
def QuadraticForm.RepresentsZeroPadically {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
    dotProduct x (mulVec (M.map (fun q : ℚ => (q : ℚ_[p]))) x) = 0

/-- **Diagonalization of nondegenerate quadratic forms over $\mathbb{Q}$.** Any nondegenerate
quadratic form $Q$ over $\mathbb{Q}$ in $n$ variables is equivalent (via a linear change of
coordinates) to a diagonal weighted sum of squares $\sum w_i x_i^2$ with all $w_i \neq 0$. -/
end Corollary112General

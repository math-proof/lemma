/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem11_1
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertProductFormula
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
import Def.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
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


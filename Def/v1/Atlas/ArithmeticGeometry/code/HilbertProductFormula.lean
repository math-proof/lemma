/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertProductFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertBilinear
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertBilinear
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol2Adic
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
open HilbertSymbol


noncomputable section

/-- Inclusion of rational units into real units: $\mathbb{Q}^\times \to \mathbb{R}^\times$. -/
def ratToRealUnits (a : ℚˣ) : ℝˣ :=
  Units.mk0 ((a : ℚ) : ℝ) (by exact_mod_cast a.ne_zero)

/-- Inclusion of rational units into $p$-adic units: $\mathbb{Q}^\times \to \mathbb{Q}_p^\times$. -/
def ratToQpUnits (p : ℕ) [Fact (Nat.Prime p)] (a : ℚˣ) : ℚ_[p]ˣ :=
  Units.mk0 ((a : ℚ) : ℚ_[p]) (by exact_mod_cast a.ne_zero)

/-- The Hilbert symbol $(a, b)_\infty$ at the infinite (archimedean) place,
computed by viewing $a, b \in \mathbb{Q}^\times$ as elements of $\mathbb{R}^\times$. -/
def hilbertAtInfty (a b : ℚˣ) : ℤ :=
  realHilbertSymbol (ratToRealUnits a) (ratToRealUnits b)

/-- The Hilbert symbol $(a, b)_p$ at the prime $p$, computed by viewing
$a, b \in \mathbb{Q}^\times$ as elements of $\mathbb{Q}_p^\times$. -/
def hilbertAtPrime (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚˣ) : ℤ :=
  padicHilbertSymbol p (ratToQpUnits p a) (ratToQpUnits p b)

/-- The global Hilbert product over all places: $\prod_v (a, b)_v$ where $v$ ranges over
$\{\infty\} \cup \{p : p \text{ prime}\}$. By the product formula (Theorem 10.11), this always
equals $1$. The product over primes is a `finprod` (well-defined by `hilbert_product_formula_finite_support`). -/
def globalHilbertProduct (a b : ℚˣ) : ℤ :=
  hilbertAtInfty a b *
  ∏ᶠ (p : Nat.Primes),
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    hilbertAtPrime p.val a b

end

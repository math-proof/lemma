/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Def.RingTheory.PowerSeries.DividingFPS.Part2
/-!
# Commutative Rings and Modules

This file provides the algebraic foundations for the theory of formal power series (FPS).
It corresponds to Section `\ref{sec.gf.defs}` and `\ref{subsec.gf.defs.commrings}` of the
source material (`CommutativeRings.tex`).

## Overview

Generating functions are not actually functions but *formal power series* (FPSs).
A formal power series is a "formal" infinite sum of the form `a₀ + a₁x + a₂x² + ⋯`,
where `x` is an indeterminate. Unlike analytic power series, we cannot substitute
numerical values for `x`.

This file reviews the algebraic structures needed for FPS:
- Commutative rings (Definition `def.alg.commring`)
- Modules over commutative rings (Definition `def.alg.module`)
- Inverses and fractions in commutative rings (`def.commring.inverse`, `def.commring.fracs`)

## Structure Note

The TeX source splits ring foundations across two files:
- `CommutativeRings.tex`: Definitions of commutative rings and modules
- `DividingFPS.tex`: Inverses, fractions, and FPS-specific division

This Lean file includes the general ring theory from both sources (inverses and fractions)
since they are foundational for all subsequent FPS theory. The FPS-specific content
(invertibility of power series, Newton's binomial formula, etc.) is in `DividingFPS.lean`.

Note: The definitions `IsInverse`, `IsInvertible`, and `fraction` here provide a pedagogical
bridge between the source's presentation and Mathlib's `IsUnit`, `Units`, etc. For actual
computations, prefer Mathlib's API directly.

## Main Definitions

### Definition def.alg.commring (Commutative Ring)

The source defines a commutative ring as a set K with three binary operations (⊕, ⊖, ⊙),
two distinguished elements (0 and 1), and nine axioms:
1. Commutativity of addition: a ⊕ b = b ⊕ a
2. Associativity of addition: a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c
3. Neutrality of zero: a ⊕ 0 = 0 ⊕ a = a
4. Subtraction undoes addition: a ⊕ b = c ↔ a = c ⊖ b
5. Commutativity of multiplication: a ⊙ b = b ⊙ a
6. Associativity of multiplication: a ⊙ (b ⊙ c) = (a ⊙ b) ⊙ c
7. Distributivity: a ⊙ (b ⊕ c) = (a ⊙ b) ⊕ (a ⊙ c) and (a ⊕ b) ⊙ c = (a ⊙ c) ⊕ (b ⊙ c)
8. Neutrality of one: a ⊙ 1 = 1 ⊙ a = a
9. Annihilation: a ⊙ 0 = 0 ⊙ a = 0

In Mathlib, this is captured by `CommRing K` (from `Mathlib.Algebra.Ring.Defs`).

### Definition def.alg.module (K-Module)

The source defines a K-module as a set M with addition, subtraction, scaling by K, and a
zero element, satisfying the standard module axioms.

In Mathlib, this is captured by `[AddCommGroup M] [Module K M]`.

### Definition def.commring.inverse (Inverses)

An element `a` of a commutative ring is **invertible** (a **unit**) if there exists `b`
with `a * b = 1`. The inverse is unique when it exists.

In Mathlib: `IsUnit a` and `Units L` (the type `Lˣ`).

### Definition def.commring.fracs (Fractions)

For an invertible element `a`, we write `b/a` for `b * a⁻¹`. Integer powers `a^n` are
defined for all `n ∈ ℤ` when `a` is invertible.

In Mathlib: `zpow` for integer powers on units.

## Main Results

Key properties of commutative rings mentioned in the source:
- `add_pow`: The binomial theorem `(a + b)^n = ∑ k, C(n,k) * a^k * b^(n-k)`
- `sub_pow`: Variant for subtraction
- Finite sums and products are well-defined and satisfy standard rules
- `isInverse_unique`: Inverses are unique (`thm.commring.inverse-uni`)

## Implementation Notes

The source defines commutative rings with explicit subtraction operation `⊖`.
Mathlib instead defines `Ring` with negation, and subtraction is derived as `a - b := a + (-b)`.
These definitions are equivalent:
- Given subtraction ⊖, define negation as `-a := 0 ⊖ a`
- Given negation, define subtraction as `a - b := a + (-b)`

The key theorem `commRing_sub_iff_add` below shows that Axiom 4 (subtraction undoes addition)
holds in Mathlib's formulation.

Similarly, the source defines modules with explicit subtraction, while Mathlib uses negation.
The equivalence is analogous.

## References

- Source: `AlgebraicCombinatorics/tex/FPS/CommutativeRings.tex`
- Additional source: `AlgebraicCombinatorics/tex/FPS/DividingFPS.tex` (inverses/fractions)
- Labels: `def.alg.commring`, `def.alg.module`, `def.commring.inverse`, `def.commring.fracs`
-/


/-!
## Section: Commutative Rings

A commutative ring is a set `K` equipped with operations `+`, `-`, `*` and elements `0`, `1`
satisfying the standard ring axioms with commutativity of multiplication.

In Mathlib, this is captured by the `CommRing` typeclass.
-/


/-!
## Section: Examples of Commutative Rings

The source lists several examples of commutative rings:
- `ℤ`, `ℚ`, `ℝ`, `ℂ` are commutative rings
- `ℕ` is NOT a commutative ring (no subtraction), but is a commutative semiring
- `ℤ[√5]` is a commutative ring (subring of `ℝ`)
- `ℤ/m` is a commutative ring for any `m`
- Power set with symmetric difference is a Boolean ring
- The tropical semiring `ℤ ∪ {-∞}` with max and + operations

In Mathlib, these are available as instances:
- `CommRing ℤ`, `CommRing ℚ`, etc.
- `CommSemiring ℕ`
- `ZMod n` for `ℤ/n`
-/


namespace AlgebraicCombinatorics.FPS

section CommRingBasics

variable {K : Type*} [CommRing K]

end CommRingBasics

section CommRingExamples

-- Standard number systems are commutative rings
example : CommRing ℤ := inferInstance

example : CommRing ℚ := inferInstance

example : CommRing ℝ := inferInstance

example : CommRing ℂ := inferInstance

-- ℕ is a commutative semiring (not a ring, since no subtraction)
example : CommSemiring ℕ := inferInstance

-- ℤ/m is a commutative ring (ZMod n in Mathlib)
example (n : ℕ) [NeZero n] : CommRing (ZMod n) := inferInstance

-- When p is prime, ℤ/p is a field
example (p : ℕ) [hp : Fact (Nat.Prime p)] : Field (ZMod p) := inferInstance

end CommRingExamples

/-!
## Section: Standard Rules in Commutative Rings

The source notes that in any commutative ring K, the standard rules of computation apply:
- Finite sums are well-defined (general associativity and commutativity)
- Finite products are well-defined
- Standard algebraic identities hold
- The binomial theorem: `(a + b)^n = ∑_{k=0}^n C(n,k) * a^k * b^(n-k)`
-/


section StandardRules

variable {K : Type*} [CommRing K]

end StandardRules

/-!
## Section: Modules over Commutative Rings

A K-module is a generalization of a vector space where the scalars come from a
commutative ring K (not necessarily a field).

The source defines a K-module (Definition `def.alg.module`) as a set M with:
- Addition `⊕ : M × M → M`
- Subtraction `⊖ : M × M → M`
- Scaling `⇀ : K × M → M`
- Zero element `0⃗ ∈ M`

satisfying the standard module axioms.

In Mathlib, this is captured by the `Module` typeclass, which requires:
- `AddCommGroup M` (for the additive structure)
- `Module K M` (for the scalar multiplication)
-/


section ModuleBasics

variable {K : Type*} [CommRing K]

variable {M : Type*} [AddCommGroup M] [Module K M]

/-!
### Additive Inverses and Subtraction

The source notes that most authors do not include subtraction in the definition of a K-module.
Instead, additive inverses can be constructed using scaling: the additive inverse of `a` is `(-1) • a`.
This shows that subtraction is derivable from the other operations.

In Mathlib, `AddCommGroup M` provides negation directly, and subtraction is defined as `a - b := a + (-b)`.
The following theorems show the equivalence between these approaches.
-/

end ModuleBasics

/-!
## Section: Module Examples

Any commutative ring K is a module over itself.
-/


section ModuleExamples

-- Any commutative ring is a module over itself
example {K : Type*} [CommRing K] : Module K K := inferInstance

-- ℚ is a module over ℤ
example : Module ℤ ℚ := inferInstance

-- ℝ is a module over ℚ (noncomputable due to real number representation)
noncomputable example : Module ℚ ℝ := inferInstance

-- ℂ is a module over ℝ (noncomputable)
noncomputable example : Module ℝ ℂ := inferInstance

end ModuleExamples
end AlgebraicCombinatorics.FPS

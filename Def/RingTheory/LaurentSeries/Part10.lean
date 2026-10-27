/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.Partition.NPartition
import Theorem.RingTheory.LaurentSeries.Part8
open scoped LaurentPolynomial

/-!
# Laurent Power Series

This file formalizes the content from Section `sec.gf.laure` of the textbook,
covering Laurent power series and related concepts.

## Main Definitions

* `BinaryRepresentation` - A binary representation of a nonnegative integer
* `BalancedTernaryRepresentation` - A balanced ternary representation of an integer
* `DoublyInfinitePowerSeries` - The K-module K[[x^±]] of all families indexed by ℤ
* `DoublyInfinitePowerSeries.IsLaurentSeries` - Predicate for when a doubly infinite
  power series is a Laurent series (Definition `def.fps.laure.lauser`)
* We also use Mathlib's `LaurentPolynomial` for K[x^±] and `LaurentSeries` for K((x))

## Main Results

* `binaryRepresentation_unique` - Each n ∈ ℕ has a unique binary representation
* `balancedTernaryRepresentation_unique` - Each integer has a unique balanced ternary representation
* `isLaurentSeries_ofLaurentSeries` - Mathlib's LaurentSeries satisfies our IsLaurentSeries predicate
* `toLaurentSeries_ofLaurentSeries` / `ofLaurentSeries_toLaurentSeries` - Round-trip equivalence
  showing our definition matches Mathlib's
* `Int.isPWO_of_bddBelow` - Bounded below subsets of ℤ are partially well-ordered
* Properties of Laurent polynomials and Laurent series from Mathlib

## References

* [Grinberg, *Algebraic Combinatorics*], Section on Laurent power series
-/


noncomputable section

namespace AlgebraicCombinatorics

section LaurentSeriesSection

variable (K : Type*) [CommRing K]

/-- Helper monoid homomorphism: maps n ∈ ℤ (as a multiplicative element) to the single
Hahn series x^n. This is used to construct the Laurent polynomial embedding. -/
def singleMonoidHom : Multiplicative ℤ →* LaurentSeries K where
  toFun n := HahnSeries.single (Multiplicative.toAdd n) 1
  map_one' := rfl
  map_mul' := by
    intro x y
    have h : Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    simp only [h, HahnSeries.single_mul_single, one_mul]

/-- The ring homomorphism from Laurent polynomials to Laurent series.
This embeds K[x^±] into K((x)) by mapping each Laurent polynomial to the corresponding
Laurent series with the same coefficients.

This is mentioned after Theorem `thm.fps.laure.lauser-ring`. -/
def laurentPolyToSeries : K[T;T⁻¹] →+* LaurentSeries K :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C (singleMonoidHom K)
    (by
      intro x y
      simp only [HahnSeries.C, singleMonoidHom, Commute, SemiconjBy]
      simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
      simp [add_comm])

end LaurentSeriesSection

/-! ## Module Structure on K[[x^±]]

While K[[x^±]] is not a ring, it has a K[x^±]-module structure.
A Laurent polynomial can be multiplied with any doubly infinite power series.

This corresponds to the discussion in "A K[x^±]-module structure on K[[x^±]]".
-/


section ModuleStructure

variable {K : Type*} [CommRing K] [Nontrivial K]

/-- The action of a Laurent polynomial on a doubly infinite power series.

The product (∑ b_n x^n) · (∑ a_n x^n) = (∑ c_n x^n) where c_n = ∑_{i ∈ ℤ} a_i b_{n-i}.
This sum is finite because the Laurent polynomial has finite support.

This makes K[[x^±]] into a K[x^±]-module. -/
def laurentPolynomialSmul (p : K[T;T⁻¹]) (f : DoublyInfinitePowerSeries K) :
    DoublyInfinitePowerSeries K :=
  fun n => p.coeff.sum fun i b => b * f (n - i)

end ModuleStructure

/-! ## k-bounded Balanced Ternary Representations

A balanced ternary representation is k-bounded if all digits beyond position k are zero.
This is used in the rigorous proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`.
-/


/-- A balanced ternary representation is k-bounded if b_{k+1} = b_{k+2} = ... = 0. -/
def BalancedTernaryRepresentation.isBounded {n : ℤ} (r : BalancedTernaryRepresentation n)
    (k : ℕ) : Prop :=
  ∀ i > k, r.digits i = 0

end AlgebraicCombinatorics
end

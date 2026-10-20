/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace MathlibExt.GroupTheory.FiniteGroupConvolutionWanted

/-!
# Convolution of functions on a finite group

The convolution product on complex-valued functions on a finite group, with
its monoid structure and the Fourier-side diagonalization: pairing the
convolution against a one-dimensional character splits as a product.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution" (reference-only, no Lean formalization);
A. Terras, Fourier Analysis on Finite Groups and Applications, Ch. 1–2
(convolution on finite groups and its Fourier transform).
-/

/-- Convolution of complex-valued functions on a finite group. -/
def conv {G : Type*} [Group G] [Fintype G] (f g : G → ℂ) : G → ℂ :=
  fun x => ∑ y : G, f y * g (y⁻¹ * x)

private theorem conv_assoc_inner {G : Type*} [Group G] [Fintype G]
    (g h : G → ℂ) (z x : G) :
    (∑ y : G, g (z⁻¹ * y) * h (y⁻¹ * x)) =
      ∑ w : G, g w * h (w⁻¹ * (z⁻¹ * x)) := by
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w => ?_
  simp [mul_assoc]

private theorem conv_assoc_apply {G : Type*} [Group G] [Fintype G]
    (f g h : G → ℂ) (x : G) : conv (conv f g) h x = conv f (conv g h) x := by
  simp only [conv]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, conv_assoc_inner]

/--
Convolution is associative.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 1 (the group algebra).

Proves `Wanted` entry `conv_assoc`.

Proof: Expand into double sums, swap them, and reindex by left multiplication,
following the finite group-algebra argument in Terras, Ch. 1.
-/
theorem conv_assoc {G : Type*} [Group G] [Fintype G]
    (f g h : G → ℂ) : conv (conv f g) h = conv f (conv g h) := by
  funext x
  exact conv_assoc_apply f g h x

private theorem conv_single_one_apply {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (f : G → ℂ) (x : G) :
    conv (Pi.single (1 : G) (1 : ℂ)) f x = f x := by
  simp [conv, Pi.single_apply]

/--
The delta function at the identity is a left identity for convolution.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 1 (identity of the group algebra).

Proves `Wanted` entry `conv_single_one`.

Proof: Expand the convolution and collapse the sum at the unique nonzero value
of `Pi.single`, following the identity-element argument in Terras, Ch. 1.
-/
theorem conv_single_one {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (f : G → ℂ) : conv (Pi.single (1 : G) (1 : ℂ)) f = f := by
  funext x
  exact conv_single_one_apply f x

private theorem conv_comm_apply {G : Type*} [CommGroup G] [Fintype G]
    (f g : G → ℂ) (x : G) : conv f g x = conv g f x := by
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp [mul_comm]

/--
Convolution is commutative on abelian groups.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2 (commutative group algebra of an abelian group).

Proves `Wanted` entry `conv_comm_of_comm`.

Proof: Reindex by `y ↦ y⁻¹ * x` and use commutativity in the group and in `ℂ`,
as in the commutative group-algebra argument in Terras, Ch. 2.
-/
theorem conv_comm_of_comm {G : Type*} [CommGroup G] [Fintype G]
    (f g : G → ℂ) : conv f g = conv g f := by
  funext x
  exact conv_comm_apply f g x

private theorem conv_charPair_inner {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (g : G → ℂ) (y : G) :
    (∑ x : G, φ x * g (y⁻¹ * x)) = φ y * ∑ z : G, φ z * g z := by
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  simp [map_mul, Finset.mul_sum, mul_assoc]

private theorem conv_charPair_apply {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (f g : G → ℂ) :
    (∑ x : G, φ x * conv f g x) =
      (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
  simp only [conv]
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    (∑ x : G, φ x * (f y * g (y⁻¹ * x))) =
        f y * ∑ x : G, φ x * g (y⁻¹ * x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    _ = f y * (φ y * ∑ z : G, φ z * g z) := by rw [conv_charPair_inner]
    _ = ∑ z : G, (φ y * f y) * (φ z * g z) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl

/--
Convolution theorem, coefficient form: pairing a convolution against a
one-dimensional character splits as a product of pairings.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "convolution"; A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2–3 (the Fourier transform takes convolution to pointwise
products).

Proves `Wanted` entry `charPair_conv`.

Proof: Swap the finite sums, reindex by `x = y * z`, and use `map_mul` to
factor the character pairing, following Terras, Ch. 2–3.
-/
theorem charPair_conv {G : Type*} [Group G] [Fintype G]
    (φ : G →* ℂ) (f g : G → ℂ) :
    (∑ x : G, φ x * conv f g x) =
      (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
  exact conv_charPair_apply φ f g

end MathlibExt.GroupTheory.FiniteGroupConvolutionWanted

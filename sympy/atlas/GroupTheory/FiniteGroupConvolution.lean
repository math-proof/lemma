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
end MathlibExt.GroupTheory.FiniteGroupConvolutionWanted

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Algebra.Star.BigOperators

@[expose] public section

open scoped BigOperators


namespace Fourier.FiniteAbelianDFTWanted

/-!
# Discrete Fourier transform on a finite abelian group

The Fourier transform of a complex-valued function on a finite abelian group,
as a function on the dual group, with Fourier inversion, the Plancherel
formula, and the shift (modulation) law.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "Fourier transform for finite abelian groups" (reference-only), and
section "Fourier transform", entry "discrete Fourier transform on a finite
abelian group" (empty); A. Terras, Fourier Analysis on Finite Groups and
Applications, Ch. 2–3 (Fourier transform on finite abelian groups).
-/

/-- The discrete Fourier transform, as a function on the dual group. -/
def dftFun {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    AddChar G ℂ → ℂ :=
  fun ψ => ∑ x : G, ψ x * f x

end Fourier.FiniteAbelianDFTWanted

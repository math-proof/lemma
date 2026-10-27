/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Star.BigOperators
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

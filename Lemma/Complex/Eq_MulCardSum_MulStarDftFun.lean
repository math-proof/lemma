import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FiniteAbelianDFT
open Fourier.FiniteAbelianDFTWanted


/--
[dft_inversion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FiniteAbelianDFT.lean)
-/
@[path]
private lemma dft_inversion_eq
-- given
  {G : Type*} [AddCommGroup G] [Fintype G]
  (f : G → ℂ)
  (x : G) :
-- imply
  f x = (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, star (ψ x) * dftFun f ψ := by
-- proof
  apply dft_inversion f x


-- created on 2026-10-10
-- updated on 2026-10-24

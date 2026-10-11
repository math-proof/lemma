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

/--
[dft_plancherel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FiniteAbelianDFT.lean)
-/
@[path]
private lemma dft_plancherel_eq
-- given
  {G : Type*} [AddCommGroup G] [Fintype G]
  (f g : G → ℂ) :
-- imply
  (∑ x : G, star (f x) * g x) = (Fintype.card G : ℂ)⁻¹ *
    ∑ ψ : AddChar G ℂ, star (dftFun f ψ) * dftFun g ψ := by
-- proof
  apply dft_plancherel f g

/--
[dftFun_translate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FiniteAbelianDFT.lean)
-/
@[path]
private lemma dft_fun_translate_eq
-- given
  {G : Type*} [AddCommGroup G] [Fintype G]
  (f : G → ℂ)
  (t : G)
  (ψ : AddChar G ℂ) :
-- imply
  dftFun (fun x => f (x - t)) ψ = ψ t * dftFun f ψ := by
-- proof
  apply dftFun_translate f t ψ

-- created on 2026-10-10

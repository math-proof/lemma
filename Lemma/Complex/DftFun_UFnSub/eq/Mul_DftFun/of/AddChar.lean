import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FiniteAbelianDFT
open Fourier.FiniteAbelianDFTWanted


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
-- updated on 2026-10-24

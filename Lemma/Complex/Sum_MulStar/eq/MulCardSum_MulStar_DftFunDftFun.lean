import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.FiniteAbelian.FiniteAbelianDFT
open Fourier.FiniteAbelianDFTWanted


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


-- created on 2026-10-10
-- updated on 2026-10-26

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/FiniteAbelianDFT.lean -/


import sympy.atlas.Analysis.Fourier.FiniteAbelianDFT
import Mathlib.Analysis.Complex.Norm
import Mathlib.Basic.Complex.BigOperators

open scoped BigOperators

namespace MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

-- Inverting the delta function at zero recovers character orthogonality.
example {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (x : G) :
    (∑ ψ : AddChar G ℂ, star (ψ x)) =
      if x = 0 then (Fintype.card G : ℂ) else 0 := by
  classical
  let δ : G → ℂ := fun y => if y = 0 then 1 else 0
  have hδ (ψ : AddChar G ℂ) : dftFun δ ψ = 1 := by
    simp [δ, dftFun]
  have hscaled := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z)
    (dft_inversion δ x).symm
  have hcard : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa [δ, hδ, hcard, mul_assoc] using hscaled

-- Plancherel yields Parseval's identity for squared complex norms.
example {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℂ) :
    (∑ x : G, ‖f x‖ ^ 2) = (Fintype.card G : ℝ)⁻¹ *
      ∑ ψ : AddChar G ℂ, ‖dftFun f ψ‖ ^ 2 := by
  have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    calc
      ((‖z‖ ^ 2 : ℝ) : ℂ) = (Complex.normSq z : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = z * star z := (Complex.mul_conj z).symm
      _ = star z * z := mul_comm _ _
  apply Complex.ofReal_inj.mp
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, hnorm] using dft_plancherel f f

-- Two successive translations multiply the transform by the character of their sum.
example {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (s t : G) (ψ : AddChar G ℂ) :
    dftFun (fun x => f ((x - t) - s)) ψ = ψ (s + t) * dftFun f ψ := by
  calc
    dftFun (fun x => f ((x - t) - s)) ψ =
        ψ t * dftFun (fun x => f (x - s)) ψ :=
      dftFun_translate (fun x => f (x - s)) t ψ
    _ = ψ t * (ψ s * dftFun f ψ) := by
      rw [dftFun_translate f s ψ]
    _ = ψ (s + t) * dftFun f ψ := by
      rw [AddChar.map_add_eq_mul]
      ring

end MathlibExt.Analysis.Fourier.FiniteAbelianDFTWanted

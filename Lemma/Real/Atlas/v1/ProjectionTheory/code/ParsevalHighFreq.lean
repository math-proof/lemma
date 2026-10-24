import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.ParsevalHighFreq
open Finset Complex ZMod ProjectionTheory


namespace ProjectionTheory

/--
[dft_highFreqPart_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalHighFreq.lean)
-/
@[path]
lemma dft_highFreqPart_zero
  {p : ℕ}
  [NeZero p]
  {g : ZMod p → ℂ} :
-- imply
  𝓕 (highFreqPart g) 0 = 0 := by
-- proof
  simp only [dft_apply_zero, highFreqPart, sum_sub_distrib, sum_const, card_univ, ZMod.card]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [nsmul_eq_mul]
  field_simp
  ring

end ProjectionTheory

namespace ProjectionTheory

/--
[dft_highFreqPart_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/ParsevalHighFreq.lean)
-/
@[path]
lemma dft_highFreqPart_ne_zero
  {p : ℕ}
  [NeZero p]
  {g : ZMod p → ℂ}
  {α : ZMod p}
-- given
  (hα : α ≠ 0) :
-- imply
  𝓕 (highFreqPart g) α = 𝓕 g α := by
-- proof
  simp only [highFreqPart, dft_apply, smul_eq_mul]
  have hfunc : (fun j => (stdAddChar (-(j * α)) : ℂ) * (g j - (↑p)⁻¹ * ∑ b, g b)) =
    (fun j => (stdAddChar (-(j * α)) : ℂ) * g j -
      (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b)) := by
    ext; ring
  rw [hfunc, sum_sub_distrib]
  suffices h : ∑ j : ZMod p, (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b) = 0 by
    simp [h]
  have hcomm : (fun j => (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b)) =
    (fun j => ((↑p)⁻¹ * ∑ b, g b) * (stdAddChar (-(j * α)) : ℂ)) := by
    ext; ring
  rw [hcomm, ← mul_sum]
  suffices hchar : ∑ j : ZMod p, (stdAddChar (-(j * α)) : ℂ) = 0 by
    rw [hchar, mul_zero]
  have key := AddChar.sum_mulShift (-(α : ZMod p)) (isPrimitive_stdAddChar p)
  simp only [neg_eq_zero, hα, ↓reduceIte, Nat.cast_zero] at key
  convert key using 1
  congr 1; ext j
  ring_nf
end ProjectionTheory
section PlancherelAxiom
open Finset Complex ZMod
/-- **Plancherel's identity on $\mathbb{Z}/p\mathbb{Z}$.** For `g : ZMod p → ℂ`,
$$p \sum_{a \in \mathbb{Z}/p} |g(a)|^2 = \sum_{\alpha \in \mathbb{Z}/p} |\hat g(\alpha)|^2.$$ -/
end PlancherelAxiom
namespace ProjectionTheory
open Finset Complex ZMod
variable {p : ℕ} [NeZero p]
/-- **Parseval applied to the high-frequency part $f_h$.** The $L^2$ mass of the
high-frequency part is captured by the non-zero Fourier modes of `g`:
$$p \sum_{a} |g_h(a)|^2 = \sum_{\alpha \neq 0} |\hat g(\alpha)|^2.$$ -/

end ProjectionTheory


-- created on 2026-10-23

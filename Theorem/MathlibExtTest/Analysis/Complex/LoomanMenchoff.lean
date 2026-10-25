/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/LoomanMenchoff.lean -/

import Theorem.Analysis.Complex.LoomanMenchoff.Part6
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow


namespace MathlibExtTest.Analysis.Complex.LoomanMenchoff

open Set

open MetaMathlibExt

-- The theorem handles a nonlinear polynomial with all four partial derivatives computed.
example : DifferentiableOn ℂ (fun z : ℂ ↦ z ^ 2) univ := by
  apply looman_menchoff (s := univ)
    (ux := fun z ↦ 2 * z.re) (uy := fun z ↦ -2 * z.im)
    (vx := fun z ↦ 2 * z.im) (vy := fun z ↦ 2 * z.re)
  · exact isOpen_univ
  · fun_prop
  · intro z _
    have h :=
      (((hasDerivAt_const (𝕜 := ℝ) 0 z.re).add
        (hasDerivAt_id (𝕜 := ℝ) 0)).pow 2).sub_const (z.im ^ 2)
    convert h using 1 <;>
      simp [pow_two, Complex.mul_re]
  · intro z _
    have h :=
      (((hasDerivAt_const (𝕜 := ℝ) 0 z.im).add
        (hasDerivAt_id (𝕜 := ℝ) 0)).pow 2).const_sub (z.re ^ 2)
    convert h using 1 <;>
      simp [pow_two, Complex.mul_re]
  · intro z _
    have hline := (hasDerivAt_const (𝕜 := ℝ) 0 z.re).add
      (hasDerivAt_id (𝕜 := ℝ) 0)
    have h := (hline.mul_const z.im).add (hline.const_mul z.im)
    convert h using 1 <;>
      simp [pow_two, Complex.mul_im] <;>
      ring_nf
    funext t
    simp
    ring
  · intro z _
    have hline := (hasDerivAt_const (𝕜 := ℝ) 0 z.im).add
      (hasDerivAt_id (𝕜 := ℝ) 0)
    have h := (hline.const_mul z.re).add (hline.mul_const z.re)
    convert h using 1 <;>
      simp [pow_two, Complex.mul_im] <;>
      ring_nf
    funext t
    simp
    ring
  · simp
  · simp

end MathlibExtTest.Analysis.Complex.LoomanMenchoff

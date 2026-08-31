import Lemma.Complex.Eq.of.Re.Im
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Conj.eq.Square |
| comm | Complex.Square.eq.Conj |
-/
@[main, comm]
private lemma main :
-- imply
  let ω := (I * (2 * π / 3)).exp
  ~ω = ω ^ 2 := by
-- proof
  extract_lets ω
  simp only [ω]
  rw [ExpMulIDivMul2Pi3.eq.Add_MulI]
  set ω := ↑(-(1 / 2 : ℝ)) + I * ↑(√3 / 2 : ℝ)
  have hre : ω.re = -(1 / 2) := by
    simp only [ω, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  apply Eq.of.Re.Im
  ·
    simp [pow_two, mul_re, conj_re, hre, him]
    ring_nf
    erw [Real.sq_sqrt (by norm_num)]
    ring
  ·
    simp [pow_two, mul_im, conj_im, hre, him]
    ring


-- created on 2026-08-31

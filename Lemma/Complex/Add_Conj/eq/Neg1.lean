import Lemma.Complex.Eq.of.Re.Im
import Lemma.Complex.ExpMulIDivMul2Pi3.eq.Add_MulI
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Add_Conj.eq.Neg1 |
| comm | Complex.Neg1.eq.Add_Conj |
-/
@[main, comm]
private lemma main :
-- imply
  let ω := (I * (2 * π / 3)).exp
  ω + ~ω = -1 := by
-- proof
  extract_lets ω
  have hre : ω.re = -(1 / 2) := by
    simp only [ω]
    rw [ExpMulIDivMul2Pi3.eq.Add_MulI]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
    ring
  have him : ω.im = √3 / 2 := by
    simp only [ω]
    rw [ExpMulIDivMul2Pi3.eq.Add_MulI]
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  apply Eq.of.Re.Im
  ·
    simp [add_re, conj_re, hre]
    ring
  ·
    simp [add_im, conj_im, him]


-- created on 2026-08-31

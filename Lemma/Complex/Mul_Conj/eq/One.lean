import Lemma.Complex.Conj.eq.Square
import Lemma.Complex.Pow_3.eq.One
open Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Mul_Conj.eq.One |
| comm | Complex.One.eq.Mul_Conj |
-/
@[main, comm]
private lemma main :
-- imply
  let ω := (I * (2 * π / 3)).exp
  ω * ~ω = 1 := by
-- proof
  extract_lets ω
  rw [Conj.eq.Square, (by simp [pow_two, pow_three] : ω * ω ^ 2 = ω ^ 3), Pow_3.eq.One]


-- created on 2026-08-31

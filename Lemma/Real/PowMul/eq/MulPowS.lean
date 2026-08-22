import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.PowMul.eq.MulPowS |
| comm | Real.MulPowS.eq.PowMul |
-/
@[main, comm]
private lemma main
  [CommMonoid α]
  {a b : α}
  {n : ℕ} :
-- imply
  (a * b) ^ n = a ^ n * b ^ n :=
-- proof
  mul_pow a b n


-- created on 2018-08-20
-- updated on 2026-08-22

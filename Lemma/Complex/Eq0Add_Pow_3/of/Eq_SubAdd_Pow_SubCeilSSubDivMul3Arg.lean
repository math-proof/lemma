import Lemma.Complex.Eq0Add_Pow_3.of.Eq_AddMulPow_SubCeilSSubDivMul3Arg
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
-- given
  (h : x =
    let p := b - a ^ 2 / 3
    let q := 2 * a ^ 3 / 27 - a * b / 3 + c
    let ω := (I * (2 * π / 3)).exp
    let δ := 4 * p ^ 3 / 27 + q ^ 2
    let A := ∛((-q + √δ) / 2)
    let B := ∛((-q - √δ) / 2)
    let k := ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ - ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
    A * ω ^ k + B - a / 3) :
-- imply
  c + b * x + a * x ^ 2 + x ^ 3 = 0 := by
-- proof
  extract_lets p q ω δ A B k at h
  let z := A * ω ^ k + B
  have hz : q + p * z + z ^ 3 = 0 := by
    apply Eq0Add_Pow_3.of.Eq_AddMulPow_SubCeilSSubDivMul3Arg
    extract_lets
    simp [z]
  have hx : x = z - a / 3 := by
    simpa [z] using h
  rw [hx]
  simp only [p, q] at hz ⊢
  convert hz using 1
  ring


-- created on 2018-11-20
-- updated on 2026-08-30

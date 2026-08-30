import Lemma.Complex.Eq0Add_Pow_3.of.Eq_AddMulPow_SubCeilSSubDivMul3Arg
open Complex


@[main]
private lemma main
  {x a b c : ℂ}
  {k : ℤ}
-- given
  (h₀ : (
    let p : ℂ := b - a ^ 2 / 3
    ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
      (
        let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
        let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
        let A : ℂ := ∛((-q + √δ) / 2)
        let B : ℂ := ∛((-q - √δ) / 2)
        ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉
      )) = k)
  (h₁ : x =
    let p : ℂ := b - a ^ 2 / 3
    let q : ℂ := 2 * a ^ 3 / 27 - a * b / 3 + c
    let ω : ℂ := (I * (2 * π / 3)).exp
    let δ : ℂ := 4 * p ^ 3 / 27 + q ^ 2
    let A : ℂ := ∛((-q + √δ) / 2)
    let B : ℂ := ∛((-q - √δ) / 2)
    A * ω ^ k + B - a / 3):
-- imply
  c + b * x + a * x ^ 2 + x ^ 3 = 0 := by
-- proof
  extract_lets p q δ A B at h₀
  extract_lets ω at h₁
  let z : ℂ := A * ω ^ k + B
  have hz : q + p * z + z ^ 3 = 0 := by
    apply Eq0Add_Pow_3.of.Eq_AddMulPow_SubCeilSSubDivMul3Arg
    extract_lets
    have hkceil :
        ⌈3 * arg (-p / 3) / (2 * π) - 1 / 2⌉ -
          ⌈3 * arg (A * B) / (2 * π) - 1 / 2⌉ =
          k := by
      simpa using h₀
    simp only [z]
    rw [← hkceil]
  have hx : x = z - a / 3 := by
    simpa [z] using h₁
  rw [hx]
  simp only [p, q] at hz ⊢
  convert hz using 1
  ring


-- created on 2018-11-10
-- updated on 2026-08-30

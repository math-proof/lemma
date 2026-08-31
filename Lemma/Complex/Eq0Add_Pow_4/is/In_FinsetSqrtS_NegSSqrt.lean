import Lemma.Complex.Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0
import Lemma.Complex.EqSquare.is.In_FinsetSqrt_NegSqrt
import Lemma.Set.In_Finset.is.OrEqS
import Lemma.Set.In_Insert.is.Eq.ou.In
open Complex Set


/--
[Biquadratic (even quartic) formula](https://en.wikipedia.org/wiki/Quartic_equation#Biquadratic_equation)

| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq0Add_Pow_4.is.In_FinsetSqrtS_NegSSqrt |
| comm | Complex.In_FinsetSqrtS_NegSSqrt.is.Eq0Add_Pow_4 |
| mp | Complex.In_FinsetSqrtS_NegSSqrt.of.Eq0Add_Pow_4 |
| mpr | Complex.Eq0Add_Pow_4.of.In_FinsetSqrtS_NegSSqrt |
-/
@[main, comm, mp, mpr]
private lemma main
  {x α γ : ℂ} :
-- imply
  γ + α * x ^ 2 + x ^ 4 = 0 ↔
    let Δ := α ^ 2 - 4 * γ
    x ∈ ({√((√Δ - α) / 2), √((-√Δ - α) / 2), -√((√Δ - α) / 2), -√((-√Δ - α) / 2)} : Set ℂ) := by
-- proof
  extract_lets Δ
  rw [(by ring : γ + α * x ^ 2 + x ^ 4 = γ + α * (x ^ 2) + 1 * (x ^ 2) ^ 2), Eq0Add_Mul_Square.is.In_FinsetDivS_Mul2.of.Ne_0 (x := x ^ 2) one_ne_zero]
  extract_lets Δq
  rw [(by grind : Δq = Δ)]
  rw [(by ring : (-α + √Δ) / (2 * (1 : ℂ)) = (√Δ - α) / 2)]
  rw [(by ring : (-α - √Δ) / (2 * (1 : ℂ)) = (-√Δ - α) / 2)]
  rw [In_Finset.is.OrEqS, EqSquare.is.In_FinsetSqrt_NegSqrt, EqSquare.is.In_FinsetSqrt_NegSqrt]
  rw [In_Finset.is.OrEqS, In_Finset.is.OrEqS, or_assoc, or_left_comm (a := x = -√((√Δ - α) / 2))]
  rw [OrEqS.is.In_Finset, Eq.ou.In.is.In_Insert, Eq.ou.In.is.In_Insert]


-- created on 2018-11-26
-- updated on 2026-08-31

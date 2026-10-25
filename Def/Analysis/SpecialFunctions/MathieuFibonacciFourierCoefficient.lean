/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/MathieuFibonacciFourierCoefficient.lean -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
/-!
# Fourier series coefficient

Retained definition for concept `Fourier series coefficient`
(`jis_sem_e469cc9709bc61c7d3368fdf`), required clause from statement
`jis_730fbe152ebd86322427d06f`.
-/


namespace MetaMathlibExt

/-- Fourier cosine-series coefficient from the periodic Mathieu–Fibonacci example.

For `n ≥ 1`, this is `(2 / Real.log ((1 + Real.sqrt 5) / 2)) *
‖Complex.Gamma (1 + 2 * n * π * I / Real.log ((1 + Real.sqrt 5) / 2))‖ ^ 2`,
where `Real.log ((1 + Real.sqrt 5) / 2)` is the fixed `log φ` of the source,
so that the source periodic function is
`H x = 1 + ∑' n : {n : ℕ // 1 ≤ n}, coeff n * Real.cos (4 * n * π * x / log φ)`.

Concept `Fourier series coefficient` (`jis_sem_e469cc9709bc61c7d3368fdf`);
required clause from statement `jis_730fbe152ebd86322427d06f`. -/
noncomputable def mathieuFibonacciFourierCoefficient (n : {n : ℕ // 1 ≤ n}) : ℝ :=
  (2 / Real.log ((1 + Real.sqrt 5) / 2)) *
    ‖Complex.Gamma (1 + 2 * (n.val : ℂ) * (Real.pi : ℂ) * Complex.I /
      (Real.log ((1 + Real.sqrt 5) / 2) : ℂ))‖ ^ 2

end MetaMathlibExt

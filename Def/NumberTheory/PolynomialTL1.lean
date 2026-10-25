/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolynomialTL1.lean -/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Analysis.Calculus.Deriv.Basic


namespace MetaMathlibExt

/-- Integrand for the polynomial `T_{l-1}` (canonical name `polynomial T_{l-1}`,
concept_id `jis_sem_267c1cca81c8b3a0062a0742`, statement `jis_d5c7f2eca643e293a3405354`,
source `jis_source_34b829866c2fa232064ad7c0`): `(8 * x ^ l - S_l(x)) / (sqrt x * (4 - x))`. -/
noncomputable def TIntegrand (S : ℕ → Polynomial ℝ) (l : ℕ) (x : ℝ) : ℝ :=
  (8 * x ^ l - Polynomial.aeval x (S l)) / (Real.sqrt x * (4 - x))

/-- Predicate characterizing the polynomial family `T_{l-1}` of degree `l - 1`
(canonical name `polynomial T_{l-1}`, concept_id `jis_sem_267c1cca81c8b3a0062a0742`,
statement `jis_d5c7f2eca643e293a3405354`, source `jis_source_34b829866c2fa232064ad7c0`):
`T 0 = 0` (i.e. `T_{-1}(x) := 0`), degree clause for `l ≥ 1` with `T l ≠ 0`,
and the antiderivative clause `2 * sqrt x * T_l(x)` has derivative
`(8 * x ^ l - S_l(x)) / (sqrt x * (4 - x))` on `0 < x < 4`,
i.e. `T_{l-1}(x) = (x ^ (-1/2) / 2) ∫ integrand dx`. -/
def IsPolyTFamily (S T : ℕ → Polynomial ℝ) : Prop :=
  T 0 = 0 ∧
    (∀ l : ℕ, 1 ≤ l → (T l).natDegree = l - 1 ∧ T l ≠ 0) ∧
    ∀ l : ℕ, 1 ≤ l → ∀ x : ℝ, 0 < x → x < 4 →
      HasDerivAt (fun y : ℝ => 2 * Real.sqrt y * Polynomial.aeval y (T l))
        (TIntegrand S l x) x

end MetaMathlibExt

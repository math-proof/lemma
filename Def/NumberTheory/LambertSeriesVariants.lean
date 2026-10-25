/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LambertSeriesVariants.lean -/

import Mathlib.Analysis.Complex.Basic


namespace MetaMathlibExt

/-- Tilde summand for Gerhold's Lambert-type variant `\tilde L_m`.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f199df27bfb37c3d9b045e32`. It is indexed by `k : Nat` with
`n = k + 1`, writing `2 * k + 1` for `2 * n - 1`. -/
noncomputable def tildeLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ ((2 * k + 1) * m.val)) / ((1 + q.val ^ (2 * k + 1)) ^ (2 * m.val))

/-- Summability predicate for `\tilde L_m` using the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f199df27bfb37c3d9b045e32`. -/
noncomputable def tildeLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (tildeLMSummand q m)

/-- The family `\tilde L_m` as the `tsum` of the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f199df27bfb37c3d9b045e32`. -/
noncomputable def tildeLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (tildeLMSummand q m)

/-- Summand for Gerhold's Lambert-type variant `\hat L_m`.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. It is indexed by `k : Nat` with `n = k + 1`. -/
noncomputable def hatLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ (m.val * (k + 1))) / ((1 + q.val ^ (2 * (k + 1))) ^ m.val)

/-- Summability predicate for `\hat L_m` using the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. -/
noncomputable def hatLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (hatLMSummand q m)

/-- The family `\hat L_m` as the `tsum` of the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. -/
noncomputable def hatLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (hatLMSummand q m)

/-- Summand for Gerhold's Lambert-type variant `L_m^*`.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. It is indexed by `k : Nat` with
`n = k + 1`, writing `2 * k + 1` for `2 * n - 1`. -/
noncomputable def starLMSummand (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) (k : ℕ) : ℂ :=
  (q.val ^ ((2 * k + 1) * m.val)) / ((1 - q.val ^ (2 * k + 1)) ^ (2 * m.val))

/-- Summability predicate for `L_m^*` using the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. -/
noncomputable def starLMSummable (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : Prop :=
  Summable (starLMSummand q m)

/-- The family `L_m^*` as the `tsum` of the identical summand.
Concept `jis_sem_e9cabece6d32bf6b52d62673`, source
`jis_f69070cf1636bd79774e81a9`. -/
noncomputable def starLM (q : { q : ℂ // ‖q‖ < 1 }) (m : { m : ℕ // 1 ≤ m }) : ℂ :=
  tsum (starLMSummand q m)

end MetaMathlibExt

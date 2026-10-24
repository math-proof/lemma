/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SimsekNumber.lean -/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MetaMathlibExt

/-- Simsek numbers `y_1(n, k; lam)` in explicit finite-sum form:
    `(1 / k !) * ∑ j ∈ Finset.range (k + 1), C(k, j) * j ^ n * lam ^ j`.
    Source: equation (snmf1) of https://cs.uwaterloo.ca/journals/JIS/VOL26/Oussi/oussi9.tex;
    phrase concept `jis_term_8eae8e670c41baff4a5d1101`,
    semantic concept `jis_sem_cadb2d3c6cc457809c98725c`,
    source statement `jis_018cebafcc5d365ff500f619`. -/
noncomputable def simsekNumber (n k : Nat) (lam : ℂ) : ℂ :=
  ((k.factorial : ℂ))⁻¹ *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * (((j : ℂ) ^ n) * (lam ^ j))
end MetaMathlibExt

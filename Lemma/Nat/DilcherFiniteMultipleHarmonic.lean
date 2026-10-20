import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DilcherFiniteMultipleHarmonic
open MetaMathlibExt


/--
[dilcher_finite_multiple_harmonic_identity_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DilcherFiniteMultipleHarmonic.lean)
-/
@[path]
private lemma dilcher_finite_multiple_harmonic_identity_general_eq
  {m n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n,
    ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m) =
    ∑ js ∈ Finset.univ.filter
    (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
    (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
-- proof
  apply MetaMathlibExt.dilcher_finite_multiple_harmonic_identity_general m n hn

/--
[dilcher_finite_multiple_harmonic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DilcherFiniteMultipleHarmonic.lean)
-/
@[path]
private lemma dilcher_finite_multiple_harmonic_identity_eq
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.Icc 1 n,
    ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m) =
    ∑ js ∈ Finset.univ.filter
    (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
    (∏ i, ((js i).val + 1 : ℚ))⁻¹ := by
-- proof
  apply MetaMathlibExt.dilcher_finite_multiple_harmonic_identity m n hm hn


-- created on 2026-10-20

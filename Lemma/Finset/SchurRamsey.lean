import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SchurRamsey
open MetaMathlibExt


/--
[schur_ramsey](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SchurRamsey.lean)
-/
@[path]
private lemma schur_ramsey_eq
  :
-- imply
  ∀ r : ℕ, 1 ≤ r →
    ∃ S : ℕ, ∀ c : ℕ → Fin r, ∃ x y z : ℕ,
    x ∈ Finset.Icc 1 S ∧ y ∈ Finset.Icc 1 S ∧ z ∈ Finset.Icc 1 S ∧
    c x = c y ∧ c x = c z ∧ x + y = z := by
-- proof
  apply MetaMathlibExt.schur_ramsey


-- created on 2026-10-20

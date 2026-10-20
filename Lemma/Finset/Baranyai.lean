import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Baranyai
open MetaMathlibExt


/--
[baranyai_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Baranyai.lean)
-/
@[path]
private lemma baranyai_theorem_eq
  :
-- imply
  ∀ (n h : ℕ), h ∣ n →
    ∃ P : Finset (Finset (Finset (Fin n))),
    P.biUnion id = Finset.powersetCard h Finset.univ ∧
    (∀ M₁ ∈ P, ∀ M₂ ∈ P, M₁ ≠ M₂ → Disjoint M₁ M₂) ∧
    ∀ M ∈ P, M.biUnion id = Finset.univ ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂ := by
-- proof
  apply MetaMathlibExt.baranyai_theorem


-- created on 2026-10-20

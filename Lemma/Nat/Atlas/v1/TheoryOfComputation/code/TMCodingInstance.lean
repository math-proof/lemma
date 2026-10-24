import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.TMCodingInstance


/--
[TMCodingInstance.stdRepresentableLang](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMCodingInstance.lean)
-/
@[path]
private lemma stdRepresentableLang_eq :
-- imply
  ∀ (h : ℕ → ℕ), TMCodingInstance.stdIsComputableLang h → ∃ e : ℕ, ∀ x : ℕ, TMCodingInstance.stdLanguageOf (TMCodingInstance.stdSmn e x) = TMCodingInstance.stdLanguageOf (h x) := by
-- proof
  apply TMCodingInstance.stdRepresentableLang


-- created on 2026-10-23

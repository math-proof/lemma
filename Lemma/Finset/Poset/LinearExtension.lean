import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Poset.LinearExtension
open FinPoset


/--
[mem_linearExtensions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma mem_linearExtensions_eq
  [Fintype α] [PartialOrder α]
  {σ : α → Fin (Fintype.card α)} :
-- imply
  σ ∈ linearExtensions α ↔ Function.Bijective σ ∧ Monotone σ := by
-- proof
  apply FinPoset.mem_linearExtensions α σ

/--
[bijective_someLinearExtension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma bijective_someLinearExtension_eq
  [Fintype α] [PartialOrder α] :
-- imply
  Function.Bijective (someLinearExtension α) := by
-- proof
  apply FinPoset.bijective_someLinearExtension α

/--
[monotone_someLinearExtension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma monotone_someLinearExtension_eq
  [Fintype α] [PartialOrder α] :
-- imply
  Monotone (someLinearExtension α) := by
-- proof
  apply FinPoset.monotone_someLinearExtension α

/--
[nonempty_linearExtensions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma nonempty_linearExtensions_eq
  [Fintype α] [PartialOrder α] :
-- imply
  (linearExtensions α).Nonempty := by
-- proof
  apply FinPoset.nonempty_linearExtensions α

/--
[card_linearExtensions_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma card_linearExtensions_pos_eq
  [Fintype α] [PartialOrder α] :
-- imply
  0 < (linearExtensions α).card := by
-- proof
  apply FinPoset.card_linearExtensions_pos α

/--
[mem_maximalElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
private lemma mem_maximalElements_eq
  [PartialOrder P]
  {A : Finset P}
  {x : P} :
-- imply
  x ∈ maximalElements A ↔ x ∈ A ∧ ∀ y ∈ A, x ≤ y → y = x := by
-- proof
  apply FinPoset.mem_maximalElements A x


-- created on 2026-10-20

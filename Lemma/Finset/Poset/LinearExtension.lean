import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Poset.LinearExtension
open FinPoset


namespace FinPoset

/--
[mem_linearExtensions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma mem_linearExtensions
  [Fintype α] [PartialOrder α]
  {σ : α → Fin (Fintype.card α)} :
-- imply
  σ ∈ linearExtensions α ↔ Function.Bijective σ ∧ Monotone σ := by
-- proof
  simp only [linearExtensions, Finset.mem_filter, Finset.mem_univ, true_and]

end FinPoset

namespace FinPoset

/--
[bijective_someLinearExtension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma bijective_someLinearExtension
  [Fintype α] [PartialOrder α] :
-- imply
  Function.Bijective (someLinearExtension α) :=
-- proof
  (linExtOrderIso α).toEquiv.bijective

end FinPoset

namespace FinPoset

/--
[monotone_someLinearExtension](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma monotone_someLinearExtension
  [Fintype α] [PartialOrder α] :
-- imply
  Monotone (someLinearExtension α) :=
-- proof
  fun _ _ h =>
    (linExtOrderIso α).monotone (toLinearExtension.monotone' h)

end FinPoset

namespace FinPoset

/--
[nonempty_linearExtensions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma nonempty_linearExtensions
  [Fintype α] [PartialOrder α] :
-- imply
  (linearExtensions α).Nonempty :=
-- proof
  ⟨someLinearExtension α, by
    rw [mem_linearExtensions]
    exact ⟨bijective_someLinearExtension α, monotone_someLinearExtension α⟩⟩

end FinPoset

namespace FinPoset

/--
[card_linearExtensions_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma card_linearExtensions_pos
  [Fintype α] [PartialOrder α] :
-- imply
  0 < (linearExtensions α).card :=
-- proof
  Finset.card_pos.mpr (nonempty_linearExtensions α)

end FinPoset

namespace FinPoset

/--
[mem_maximalElements](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Poset/LinearExtension.lean)
-/
@[path]
lemma mem_maximalElements
  [PartialOrder P]
  {A : Finset P}
  {x : P} :
-- imply
  x ∈ maximalElements A ↔ x ∈ A ∧ ∀ y ∈ A, x ≤ y → y = x := by
-- proof
  simp only [maximalElements, Finset.mem_filter]

end FinPoset


-- created on 2026-10-20
-- updated on 2026-10-26

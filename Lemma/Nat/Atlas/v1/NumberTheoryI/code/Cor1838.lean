import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset BigOperators
open scoped AddChar ComplexConjugate


namespace CharacterOrthogonality

/--
[sum_char_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1838.lean)
-/
@[path]
lemma sum_char_ne_zero_iff
  [AddCommGroup G]
  [Fintype G]
  (χ : AddChar G ℂ) :
-- imply
  ∑ g : G, χ g ≠ 0 ↔ χ = 0 := by
-- proof
  classical
  rw [AddChar.sum_eq_ite, ne_eq]
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro h
    subst h
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[sum_dual_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1838.lean)
-/
@[path]
lemma sum_dual_ne_zero_iff
  [AddCommGroup G]
  [Fintype G]
  [DecidableEq G]
  (g : G) :
-- imply
  ∑ χ : AddChar G ℂ, χ g ≠ 0 ↔ g = 0 := by
-- proof
  rw [AddChar.sum_apply_eq_ite, ne_eq]
  constructor
  · intro h
    by_contra hne
    simp [hne] at h
  · intro h
    subst h
    simp [Nat.cast_ne_zero.mpr Fintype.card_ne_zero]

end CharacterOrthogonality

namespace CharacterOrthogonality

/--
[corollary_18_38](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1838.lean)
-/
@[path]
lemma corollary_18_38
  [AddCommGroup G]
  [Fintype G]
  [DecidableEq G] :
-- imply
  (∀ χ : AddChar G ℂ, ∑ g : G, χ g ≠ 0 ↔ χ = 0) ∧ (∀ g : G, ∑ χ : AddChar G ℂ, χ g ≠ 0 ↔ g = 0) :=
-- proof
  ⟨sum_char_ne_zero_iff, sum_dual_ne_zero_iff⟩
end CharacterOrthogonality
namespace Cor1838
export CharacterOrthogonality (sum_char_ne_zero_iff sum_dual_ne_zero_iff corollary_18_38)
end Cor1838



-- created on 2026-10-23

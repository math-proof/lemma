import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity
open CoxeterSystemFromDeletion Function Set


/--
[deletionCanonicalHom_map_word_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivity.lean)
-/
@[path]
private lemma deletionCanonicalHom_map_word_prod_eq
  [Group W]
  {gen : B → W}
  {word : List B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
-- imply
  let M := deletionCoxeterMatrix gen hgen_inv hgen_ne let φ := deletionCanonicalHom gen hgen_inv hgen_ne φ ((word.map M.simple).prod) = (word.map gen).prod := by
-- proof
  apply CoxeterSystemFromDeletion.deletionCanonicalHom_map_word_prod gen hgen_inv hgen_ne word

/--
[deletionCanonicalHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivity.lean)
-/
@[path]
private lemma deletionCanonicalHom_injective_eq
  [Group W]
  [Group W]
  {gen : B → W}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
  (hDel : SatisfiesDeletionConditionGen gen) :
-- imply
  Function.Injective (deletionCanonicalHom gen hgen_inv hgen_ne) := by
-- proof
  apply CoxeterSystemFromDeletion.deletionCanonicalHom_injective gen hgen_inv hgen_ne hgen_surj hDel


-- created on 2026-10-23

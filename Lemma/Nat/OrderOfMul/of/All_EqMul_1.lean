import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion
open Function Set CoxeterSystemFromDeletion


namespace Definitions
end Definitions
/--
[orderOf_mul_comm_of_involution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean)
-/
@[path]
private lemma orderOf_mul_comm_of_involution_eq
  [Group W]
  {gen : B → W}
  {s t : B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1) :
-- imply
  orderOf (gen s * gen t) = orderOf (gen t * gen s) := by
-- proof
  apply SemiconjBy.orderOf_eq
  show gen s * (gen s * gen t) = gen t * gen s * gen s
  rw [← mul_assoc, hgen_inv s, one_mul, mul_assoc, hgen_inv s, mul_one]

/--
[deletionCoxeterMatrix_isLiftable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean)
-/
@[path]
private lemma deletionCoxeterMatrix_isLiftable_eq
  [Group W]
  {gen : B → W}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
-- imply
  (deletionCoxeterMatrix gen hgen_inv hgen_ne).IsLiftable gen := by
-- proof
  apply CoxeterSystemFromDeletion.deletionCoxeterMatrix_isLiftable gen hgen_inv hgen_ne

/--
[deletionCanonicalHom_apply_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean)
-/
@[path]
private lemma deletionCanonicalHom_apply_simple_eq
  [Group W]
  {gen : B → W}
  {s : B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
-- imply
  deletionCanonicalHom gen hgen_inv hgen_ne ((deletionCoxeterMatrix gen hgen_inv hgen_ne).simple s) = gen s := by
-- proof
  apply CoxeterSystemFromDeletion.deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s

/--
[deletionCanonicalHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean)
-/
@[path]
private lemma deletionCanonicalHom_surjective_eq
  [Group W]
  {gen : B → W}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (hgen_surj : Subgroup.closure (Set.range gen) = ⊤) :
-- imply
  Function.Surjective (deletionCanonicalHom gen hgen_inv hgen_ne) := by
-- proof
  apply CoxeterSystemFromDeletion.deletionCanonicalHom_surjective gen hgen_inv hgen_ne hgen_surj


-- created on 2026-10-24

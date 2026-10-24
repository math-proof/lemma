import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.TitsForwardHelpers
open CoxeterSystemFromDeletion


/--
[deletion_coxeter_simple_eq_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/TitsForwardHelpers.lean)
-/
@[path]
private lemma deletion_coxeter_simple_eq_gen_eq
  [Group W]
  {gen : B → W}
  {s : B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
  (hDel : SatisfiesDeletionConditionGen gen) :
-- imply
  (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).simple s = gen s := by
-- proof
  apply CoxeterSystemFromDeletion.deletion_coxeter_simple_eq_gen gen hgen_inv hgen_ne hgen_surj hDel s

/--
[mulEquiv_simple_eq_toCoxeterSystem_simple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/TitsForwardHelpers.lean)
-/
@[path]
private lemma mulEquiv_simple_eq_toCoxeterSystem_simple_eq
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {s : B} :
-- imply
  cs.mulEquiv (cs.simple s) = M.toCoxeterSystem.simple s := by
-- proof
  apply CoxeterSystemFromDeletion.mulEquiv_simple_eq_toCoxeterSystem_simple cs s

/--
[deletion_coxeter_mulEquiv_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/TitsForwardHelpers.lean)
-/
@[path]
private lemma deletion_coxeter_mulEquiv_gen_eq
  [Group W]
  {gen : B → W}
  {s : B}
-- given
  (hgen_inv : ∀ s, gen s * gen s = 1)
  (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
  (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
  (hDel : SatisfiesDeletionConditionGen gen) :
-- imply
  (deletion_implies_coxeter_system gen hgen_inv hgen_ne hgen_surj hDel).mulEquiv (gen s) = (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.simple s := by
-- proof
  apply CoxeterSystemFromDeletion.deletion_coxeter_mulEquiv_gen gen hgen_inv hgen_ne hgen_surj hDel s


-- created on 2026-10-23

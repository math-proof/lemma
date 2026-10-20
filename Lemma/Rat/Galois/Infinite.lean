import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Galois.Infinite
open InfiniteGalois


/--
[topologicalClosure_eq_fixingSubgroup_fixedField](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/Infinite.lean)
-/
@[path]
private lemma topologicalClosure_eq_fixingSubgroup_fixedField_eq
  [Field k] [Field K] [Algebra k K] [IsGalois k K]
  {H : Subgroup Gal(K/k)} :
-- imply
  H.topologicalClosure = (IntermediateField.fixedField H).fixingSubgroup := by
-- proof
  apply InfiniteGalois.topologicalClosure_eq_fixingSubgroup_fixedField H


-- created on 2026-10-20

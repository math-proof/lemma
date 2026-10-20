import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.ClassFunction
open MathlibExt.GroupTheory.ClassFunctionWanted


/--
[character_isClassFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma character_isClassFunction_eq
  [Group G] [Field k]
  {V : FDRep k G} :
-- imply
  IsClassFunction V.character := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.character_isClassFunction V

/--
[IsClassFunction.eq_of_isConj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma IsClassFunction_eq_of_isConj_eq
  [Group G]
  {f : G → k}
  {x y : G}
-- given
  (hf : IsClassFunction f)
  (hxy : IsConj x y) :
-- imply
  f x = f y := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.IsClassFunction.eq_of_isConj hf hxy

/--
[isClassFunction_iff_factor_conjClasses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma isClassFunction_iff_factor_conjClasses_eq
  [Group G]
  {f : G → k} :
-- imply
  IsClassFunction f ↔ ∃ g : ConjClasses G → k, ∀ x : G, f x = g (ConjClasses.mk x) := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.isClassFunction_iff_factor_conjClasses f

/--
[classFunctionsEquivConjClasses_apply_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma classFunctionsEquivConjClasses_apply_mk_eq
  [Group G] [Field k]
  {f : classFunctions G k}
  {x : G} :
-- imply
  classFunctionsEquivConjClasses G k f (ConjClasses.mk x) = (f : G → k) x := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.classFunctionsEquivConjClasses_apply_mk f x

/--
[classFunctionsEquivConjClasses_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma classFunctionsEquivConjClasses_symm_apply_eq
  [Group G] [Field k]
  {q : ConjClasses G → k}
  {x : G} :
-- imply
  (↑((classFunctionsEquivConjClasses G k).symm q) : G → k) x = q (ConjClasses.mk x) := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.classFunctionsEquivConjClasses_symm_apply q x

/--
[finrank_classFunctions_eq_card_conjClasses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma finrank_classFunctions_eq_card_conjClasses_eq
  [Group G] [Fintype G] [Field k] :
-- imply
  Module.finrank k ↥(classFunctions G k) = Nat.card (ConjClasses G) := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.finrank_classFunctions_eq_card_conjClasses G k


-- created on 2026-10-20

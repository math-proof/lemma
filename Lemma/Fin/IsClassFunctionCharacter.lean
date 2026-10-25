import Mathlib
import sympy.Basic
import Def.GroupTheory.ClassFunction.Part2
open MathlibExt.GroupTheory.ClassFunctionWanted


/--
[character_isClassFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
@[path]
private lemma main
  [Group G] [Field k]
  {V : FDRep k G} :
-- imply
  IsClassFunction V.character :=
-- proof
  fun g h => FDRep.char_conj V g h



/--
[classFunction_eq_of_isConj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma classFunction_eq_of_isConj {G k : Type*} [Group G]
  {f : G → k} (hf : IsClassFunction f) {x y : G} (hxy : IsConj x y) : f x = f y := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
  exact (hf x h).symm



/--
[IsClassFunction.eq_of_isConj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma IsClassFunction.eq_of_isConj
  [Group G]
  {f : G → k}
  {x y : G}
-- given
  (hf : IsClassFunction f)
  (hxy : IsConj x y) :
-- imply
  f x = f y :=
-- proof
  classFunction_eq_of_isConj hf hxy



/--
[classFunctionsEquivConjClasses_apply_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma classFunctionsEquivConjClasses_apply_mk
  [Group G] [Field k]
  {f : classFunctions G k}
  {x : G} :
-- imply
  classFunctionsEquivConjClasses G k f (ConjClasses.mk x) = (f : G → k) x :=
-- proof
  rfl



/--
[classFunctionsEquivConjClasses_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma classFunctionsEquivConjClasses_symm_apply
  [Group G] [Field k]
  {q : ConjClasses G → k}
  {x : G} :
-- imply
  (↑((classFunctionsEquivConjClasses G k).symm q) : G → k) x = q (ConjClasses.mk x) :=
-- proof
  rfl



/--
[finrank_classFunctions_eq_card_conjClasses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma finrank_classFunctions_eq_card_conjClasses
  [Group G] [Fintype G] [Field k] :
-- imply
  Module.finrank k ↥(classFunctions G k) = Nat.card (ConjClasses G) := by
-- proof
  classical
  let _ : Fintype (ConjClasses G) :=
    Fintype.ofSurjective ConjClasses.mk ConjClasses.mk_surjective
  calc
    Module.finrank k ↥(classFunctions G k) = Module.finrank k (ConjClasses G → k) :=
      (classFunctionsEquivConjClasses G k).finrank_eq
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (ConjClasses G) := Fintype.card_eq_nat_card


/--
[isClassFunction_iff_factor_conjClasses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean)
-/
private lemma isClassFunction_iff_factor_conjClasses_eq
  [Group G]
  {f : G → k} :
-- imply
  IsClassFunction f ↔ ∃ g : ConjClasses G → k, ∀ x : G, f x = g (ConjClasses.mk x) := by
-- proof
  apply MathlibExt.GroupTheory.ClassFunctionWanted.isClassFunction_iff_factor_conjClasses f


-- created on 2026-10-20
-- updated on 2026-10-24

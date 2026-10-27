import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
open CategoryTheory


/--
[Theorem_1_23_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma Theorem_1_23_2
  {k : Type w}
  [Field k] :
-- imply
  (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (MonoidalTannakaData k C)) ∧ (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RightRigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (TannakaWithAntipodeData k C)) ∧ (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (TannakaHopfData k C)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H], Nonempty (BialgebraComoduleData k H)) :=
-- proof
  thm_1_23_2 k

/--
[theorem_1_23_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma theorem_1_23_2
  {k : Type w}
  [Field k] :
-- imply
  (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (MonoidalTannakaData k C)) ∧ (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RightRigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (TannakaWithAntipodeData k C)) ∧ (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C] [Linear k C] [RigidCategory C] (F : C ⥤ ModuleCat.{w} k) (hFaithful : F.Faithful) (hMono : F.PreservesMonomorphisms) (hEpi : F.PreservesEpimorphisms) (hMonoidal : F.Monoidal), Nonempty (TannakaHopfData k C)) ∧ (∀ (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H], Nonempty (BialgebraComoduleData k H)) :=
-- proof
  thm_1_23_2 k

/--
[Theorem_1_23_2_part1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma Theorem_1_23_2_part1
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  {F : C ⥤ ModuleCat.{w} k}
-- given
  (hFaithful : F.Faithful)
  (hMono : F.PreservesMonomorphisms)
  (hEpi : F.PreservesEpimorphisms)
  (hMonoidal : F.Monoidal) :
-- imply
  Nonempty (MonoidalTannakaData k C) :=
-- proof
  (thm_1_23_2 k).1 C F hFaithful hMono hEpi hMonoidal

/--
[Theorem_1_23_2_part2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma Theorem_1_23_2_part2
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  [RightRigidCategory C]
  {F : C ⥤ ModuleCat.{w} k}
-- given
  (hFaithful : F.Faithful)
  (hMono : F.PreservesMonomorphisms)
  (hEpi : F.PreservesEpimorphisms)
  (hMonoidal : F.Monoidal) :
-- imply
  Nonempty (TannakaWithAntipodeData k C) :=
-- proof
  (thm_1_23_2 k).2.1 C F hFaithful hMono hEpi hMonoidal

/--
[Theorem_1_23_2_part3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma Theorem_1_23_2_part3
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  [RigidCategory C]
  {F : C ⥤ ModuleCat.{w} k}
-- given
  (hFaithful : F.Faithful)
  (hMono : F.PreservesMonomorphisms)
  (hEpi : F.PreservesEpimorphisms)
  (hMonoidal : F.Monoidal) :
-- imply
  Nonempty (TannakaHopfData k C) :=
-- proof
  (thm_1_23_2 k).2.2.1 C F hFaithful hMono hEpi hMonoidal

/--
[Theorem_1_23_2_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_2.lean)
-/
@[path]
lemma Theorem_1_23_2_inverse
  {k : Type w}
  [Field k]
  {H : Type w}
  [Ring H]
  [Algebra k H]
  [Bialgebra k H] :
-- imply
  Nonempty (BialgebraComoduleData k H) :=
-- proof
  (thm_1_23_2 k).2.2.2 H


-- created on 2026-10-23

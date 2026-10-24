import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
open CategoryTheory


/--
[theorem_1_23_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_23_1.lean)
-/
@[path]
lemma theorem_1_23_1
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [Abelian C]
  [Linear k C]
  {F : C ⥤ ModuleCat.{w} k}
  [F.Faithful]
  [F.PreservesMonomorphisms]
  [F.PreservesEpimorphisms] :
-- imply
  Nonempty (TannakaReconstructionData k C F) :=
-- proof
  ⟨tannaka_reconstruction_categorical k C F⟩


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
open CategoryTheory CategoryTheory.Limits MonoidalCategory


/--
[Theorem_1_50_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_50_1.lean)
-/
@[path]
lemma Theorem_1_50_1
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [Preadditive C]
  [Linear k C]
  [MonoidalPreadditive C]
  [MonoidalLinear k C]
  [RigidCategory C]
  {D : Type u₁}
  [Category.{v₁} D]
  [MonoidalCategory D]
  [Abelian D]
  [Preadditive D]
  [Linear k D]
  [MonoidalPreadditive D]
  [MonoidalLinear k D]
  [RigidCategory D]
  {QTF : SurjectiveQuasiTensorFunctor k C D}
  {decompC : FiniteMultitensorDecompData k C}
  {decompD : FiniteMultitensorDecompData k D}
-- given
  (dC : FPdimFunction (C := C))
  (dD : FPdimFunction (C := D))
  (hC_pos : categoricalFPdim decompC dC > 0)
  (hD_pos : categoricalFPdim decompD dD > 0) :
-- imply
  ∀ j : decompD.I, coeffF_RC QTF decompC decompD dC j = (categoricalFPdim decompC dC / categoricalFPdim decompD dD) * dD.fpDim (decompD.simpleObj j) :=
-- proof
  CategoryTheory.thm_1_50_1 QTF decompC decompD dC dD hC_pos hD_pos


-- created on 2026-10-23

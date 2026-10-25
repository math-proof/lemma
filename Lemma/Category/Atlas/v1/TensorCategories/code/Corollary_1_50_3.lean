import Mathlib
import sympy.Basic
import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
open CategoryTheory CategoryTheory.Limits MonoidalCategory


/--
[Corollary_1_50_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_50_3.lean)
-/
@[path]
lemma Corollary_1_50_3
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
  (hD_pos : categoricalFPdim decompD dD > 0)
  (hC_int : dC.IsIntegral) :
-- imply
  dD.IsIntegral ∧ (∃ (n : ℕ), n > 0 ∧ categoricalFPdim decompC dC / categoricalFPdim decompD dD = ↑n) ∧ (∃ (n : ℕ), n > 0 ∧ ∀ j : decompD.I, coeffF_RC QTF decompC decompD dC j = ↑n * dD.fpDim (decompD.simpleObj j)) ∧ (∃ (nC nD m : ℕ), categoricalFPdim decompC dC = ↑nC ∧ categoricalFPdim decompD dD = ↑nD ∧ nD * m = nC ∧ 0 < nD ∧ 0 < m) :=
-- proof
  corollary_1_50_3 QTF decompC decompD dC dD hC_pos hD_pos hC_int


-- created on 2026-10-23

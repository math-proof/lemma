import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.Theorem_1_34_8
open CategoryTheory TensorCategories
open TensorCategories


/--
[theorem_1_34_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_34_8.lean)
-/
@[path]
lemma theorem_1_34_8
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  {QF : QuasiFiberFunctor k C} :
-- imply
  ∃ (data : QuasiBialgebraReconstructionData k C), Nonempty (MonoidalEquiv_134 C data.RepH) :=
-- proof
  tannaka_reconstruction_bialgebra_1_34_8 k C QF

/--
[theorem_1_34_8_roundtrip_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_34_8.lean)
-/
@[path]
lemma theorem_1_34_8_roundtrip_algebra
  {k : Type w}
  [Field k]
  {H : Type w}
  [Ring H]
  [Algebra k H]
  [instQB : QuasiBialgebra k H]
  [FiniteDimensional k H]
  {repData : QuasiBialgebraRepData k H}
  [instLinear : Linear k repData.RepH]
-- given
  (reconData : QuasiBialgebraReconstructionData (C := repData.RepH) k) :
-- imply
  Nonempty (reconData.H ≃ₐ[k] H) :=
-- proof
  tannaka_reconstruction_quasi_bialgebra_roundtrip_algebra k H repData reconData

/--
[Theorem_1_34_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_34_8.lean)
-/
@[path]
lemma Theorem_1_34_8
  {k : Type w}
  [Field k]
  {C : Type (w+1)}
  [Category.{w} C]
  [MonoidalCategory C]
  [Abelian C]
  [Linear k C]
  {QF : QuasiFiberFunctor k C} :
-- imply
  ∃ (data : QuasiBialgebraReconstructionData k C), Nonempty (MonoidalEquiv_134 C data.RepH) :=
-- proof
  theorem_1_34_8 k C QF


-- created on 2026-10-23

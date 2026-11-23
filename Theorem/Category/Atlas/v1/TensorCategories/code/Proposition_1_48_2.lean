module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory

public section

open CategoryTheory MonoidalCategory


/--
[Proposition_1_48_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_48_2.lean)
-/
@[path]
public theorem Proposition_1_48_2
  {k : Type w}
  [Field k]
  {C : Type u}
  [Category.{v} C]
  [MonoidalCategory C]
  [Abelian C]
  [EnoughProjectives C]
  [Linear k C]
  [RigidCategory C]
-- given
  (d : FPdimFunction (C := C)) :
-- imply
  d.IsIntegral ↔ HasQuasiFiberFunctor k C :=
-- proof
  integral_iff_hasQuasiFiberFunctor k d


-- created on 2026-10-23

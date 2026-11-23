module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.TensorCategories.code.FiberFunctor

public section

open CategoryTheory MonoidalCategory TensorCategories


namespace TensorCategories

/--
[FiberFunctor.isFaithful_1_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctor.lean)
-/
@[path]
public theorem FiberFunctor.isFaithful_1_21
  {k : Type w}
  [Field k]
  {FF : FiberFunctor k C} :
-- imply
  FF.F.Faithful :=
-- proof
  FF.faithful

end TensorCategories

namespace TensorCategories

/--
[FiberFunctor.isLeftExact_1_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctor.lean)
-/
@[path]
public theorem FiberFunctor.isLeftExact_1_21
  {k : Type w}
  [Field k]
  {FF : FiberFunctor k C} :
-- imply
  FF.F.PreservesMonomorphisms :=
-- proof
  FF.preservesMono

end TensorCategories

namespace TensorCategories

/--
[FiberFunctor.isRightExact_1_21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctor.lean)
-/
@[path]
public theorem FiberFunctor.isRightExact_1_21
  {k : Type w}
  [Field k]
  {FF : FiberFunctor k C} :
-- imply
  FF.F.PreservesEpimorphisms :=
-- proof
  FF.preservesEpi

end TensorCategories


-- created on 2026-10-23

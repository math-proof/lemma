module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5

public section

open CategoryTheory MonoidalCategory TensorCategories

universe v u v₁ u₁ w

variable {k : Type w} [Field k]
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]


namespace TensorCategories

/--
[QuasiTensorFunctor.isLeftExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem QuasiTensorFunctor.isLeftExact
  {k : Type w}
  [Field k]
  {QTF : QuasiTensorFunctor k C D} :
-- imply
  QTF.F.PreservesMonomorphisms :=
-- proof
  QTF.preservesMono

end TensorCategories

namespace TensorCategories

/--
[QuasiTensorFunctor.isRightExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem QuasiTensorFunctor.isRightExact
  {k : Type w}
  [Field k]
  {QTF : QuasiTensorFunctor k C D} :
-- imply
  QTF.F.PreservesEpimorphisms :=
-- proof
  QTF.preservesEpi

end TensorCategories

namespace TensorCategories

/--
[QuasiTensorFunctor.isFaithful](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem QuasiTensorFunctor.isFaithful
  {k : Type w}
  [Field k]
  {QTF : QuasiTensorFunctor k C D} :
-- imply
  QTF.F.Faithful :=
-- proof
  QTF.faithful

end TensorCategories

namespace TensorCategories

/--
[TensorFunctor.isLeftExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem TensorFunctor.isLeftExact
  {k : Type w}
  [Field k]
  {TF : TensorFunctor k C D} :
-- imply
  TF.F.PreservesMonomorphisms :=
-- proof
  TF.preservesMono

end TensorCategories

namespace TensorCategories

/--
[TensorFunctor.isRightExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem TensorFunctor.isRightExact
  {k : Type w}
  [Field k]
  {TF : TensorFunctor k C D} :
-- imply
  TF.F.PreservesEpimorphisms :=
-- proof
  TF.preservesEpi

end TensorCategories

namespace TensorCategories

/--
[TensorFunctor.isFaithful](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
public theorem TensorFunctor.isFaithful
  {k : Type w}
  [Field k]
  {TF : TensorFunctor k C D} :
-- imply
  TF.F.Faithful :=
-- proof
  TF.faithful

end TensorCategories

end


-- created on 2026-10-23

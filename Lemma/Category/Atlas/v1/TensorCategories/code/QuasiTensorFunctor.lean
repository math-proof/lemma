import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
open CategoryTheory MonoidalCategory TensorCategories in


namespace TensorCategories

/--
[QuasiTensorFunctor.isLeftExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean)
-/
@[path]
lemma QuasiTensorFunctor.isLeftExact
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
@[path]
lemma QuasiTensorFunctor.isRightExact
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
@[path]
lemma QuasiTensorFunctor.isFaithful
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
@[path]
lemma TensorFunctor.isLeftExact
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
@[path]
lemma TensorFunctor.isRightExact
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
@[path]
lemma TensorFunctor.isFaithful
  {k : Type w}
  [Field k]
  {TF : TensorFunctor k C D} :
-- imply
  TF.F.Faithful :=
-- proof
  TF.faithful

end TensorCategories


-- created on 2026-10-23

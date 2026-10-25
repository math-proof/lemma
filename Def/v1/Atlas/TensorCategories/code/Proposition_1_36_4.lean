/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_36_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_36_4
open scoped TensorProduct
open CategoryTheory

universe u


namespace Prop1364

variable (R : Type u) [CommSemiring R]

variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The algebra map `(ε ⊗ id) : H ⊗ H → H` used to express normalization of a bialgebra
twist. -/
noncomputable def counitTensorId :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H))

/-- The algebra map `(id ⊗ ε) : H ⊗ H → H` used to express normalization of a bialgebra
twist. -/
noncomputable def idTensorCounit :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H))

/-- The algebra map `(id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)` used in the cocycle equation. -/
noncomputable def idTensorComul :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)

/-- The algebra map `(Δ ⊗ id) : H ⊗ H → H ⊗ (H ⊗ H)` (using the associator) used in the
cocycle equation. -/
noncomputable def comulTensorId :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))

/-- The algebra inclusion `H ⊗ H ↪ H ⊗ (H ⊗ H)` sending `x ⊗ y ↦ 1 ⊗ (x ⊗ y)`, appearing as
`(1 ⊗ J)` in the cocycle equation. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- The algebra inclusion `H ⊗ H ↪ H ⊗ (H ⊗ H)` sending `x ⊗ y ↦ (x ⊗ y) ⊗ 1`, appearing as
`(J ⊗ 1)` in the cocycle equation. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end Prop1364

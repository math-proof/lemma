/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
open scoped TensorProduct
open CategoryTheory TensorCategories

universe u


namespace BialgebraTwist

variable (R : Type u) [CommSemiring R]

variable (H : Type u) [Semiring H] [Bialgebra R H]

/-- The algebra map `(ε ⊗ id) : H ⊗ H → H` collapsing the first tensor factor via
the counit. -/
noncomputable def counitTensorId :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R H) (AlgHom.id R H))

/-- The algebra map `(id ⊗ ε) : H ⊗ H → H` collapsing the second tensor factor via
the counit. -/
noncomputable def idTensorCounit :
    H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.counitAlgHom R H))

/-- The algebra map `(id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)` applying the comultiplication
to the second tensor factor. -/
noncomputable def idTensorComul :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) (Bialgebra.comulAlgHom R H)

/-- The algebra map `(Δ ⊗ id) : H ⊗ H → H ⊗ (H ⊗ H)` applying the comultiplication
to the first tensor factor, followed by the associator. -/
noncomputable def comulTensorId :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R H) (AlgHom.id R H))

/-- Right embedding `H ⊗ H → H ⊗ (H ⊗ H)` as `1 ⊗ (-)`. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- Left embedding `H ⊗ H → H ⊗ (H ⊗ H)` as `(-) ⊗ 1` followed by the associator. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end BialgebraTwist

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Class.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part2
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


namespace QuasiBialgebraTwist

variable (R : Type u) [CommSemiring R]

variable (H : Type v) [Semiring H] [Algebra R H]

/-- `(ε ⊗ Id) : H ⊗ H → H`, used in the twist counit normalization. -/
noncomputable def counitTensorId (ε : H →ₐ[R] R) : H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.lid R H).toAlgHom.comp
    (Algebra.TensorProduct.map ε (AlgHom.id R H))

/-- `(Id ⊗ ε) : H ⊗ H → H`, used in the twist counit normalization. -/
noncomputable def idTensorCounit (ε : H →ₐ[R] R) : H ⊗[R] H →ₐ[R] H :=
  (Algebra.TensorProduct.rid R R H).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R H) ε)

/-- `(Id ⊗ Δ) : H ⊗ H → H ⊗ (H ⊗ H)`, used in the formula for the twisted associator. -/
noncomputable def idTensorComul (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.map (AlgHom.id R H) Δ

/-- `(Δ ⊗ Id) : H ⊗ H → H ⊗ (H ⊗ H)`, reassociated, used in the formula for the
twisted associator. -/
noncomputable def comulTensorId (Δ : H →ₐ[R] H ⊗[R] H) :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    (Algebra.TensorProduct.map Δ (AlgHom.id R H))

/-- The embedding `x ↦ 1 ⊗ x : H ⊗ H → H ⊗ (H ⊗ H)`, realizing `1 ⊗ J` in the
twisted associator formula. -/
noncomputable def embedRight :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  Algebra.TensorProduct.includeRight

/-- The embedding `x ↦ x ⊗ 1 : H ⊗ H → H ⊗ (H ⊗ H)`, realizing `J ⊗ 1` in the
twisted associator formula. -/
noncomputable def embedLeft :
    H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H) :=
  (Algebra.TensorProduct.assoc R R R H H H).toAlgHom.comp
    Algebra.TensorProduct.includeLeft

end QuasiBialgebraTwist

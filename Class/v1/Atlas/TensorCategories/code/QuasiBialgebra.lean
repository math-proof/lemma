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
import Def.v1.Atlas.TensorCategories.code.QuasiBialgebra
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Definition 1.34.5 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-bialgebra over `R`
consists of an associative unital `R`-algebra `H` together with a coproduct
`comul : H → H ⊗ H`, a counit `counit : H → R` (both unital algebra
homomorphisms), and an invertible associator `Φ ∈ H^{⊗3}` satisfying the
quasi-coassociativity, counit and pentagon axioms. -/
class QuasiBialgebra (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H] where
  comul : H →ₐ[R] H ⊗[R] H
  counit : H →ₐ[R] R
  Φ : (H ⊗[R] (H ⊗[R] H))ˣ
  quasi_coassoc : ∀ a : H,
    QuasiBialgebra.idTensorComul R H comul a * (Φ : H ⊗[R] (H ⊗[R] H)) =
    (Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.comulTensorId R H comul a
  left_counit :
    (Algebra.TensorProduct.lid R H).toAlgHom.comp
      ((Algebra.TensorProduct.map counit (AlgHom.id R H)).comp comul) =
    AlgHom.id R H
  right_counit :
    (Algebra.TensorProduct.rid R R H).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R H) counit).comp comul) =
    AlgHom.id R H
  Φ_counit :
    QuasiBialgebra.idCounitId R H counit (Φ : H ⊗[R] (H ⊗[R] H)) = 1
  pentagon :
    (1 : H) ⊗ₜ[R] (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.idComulId R H comul (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.embedPhiRight R H (Φ : H ⊗[R] (H ⊗[R] H)) =
    QuasiBialgebra.idIdComul R H comul (Φ : H ⊗[R] (H ⊗[R] H)) *
      QuasiBialgebra.comulIdId R H comul (Φ : H ⊗[R] (H ⊗[R] H))


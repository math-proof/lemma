/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_48_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe u


namespace CategoryTheory

/-- Two finite dimensional quasi-Hopf algebras `H₁` and `H₂` over `k` are monoidally
equivalent (in the sense of their categories of finite dimensional representations) if there
is a monoidal equivalence between `QuasiRepCat k H₁` and `QuasiRepCat k H₂`. -/
def QuasiRepCatMonoidalEquiv (k : Type u) [Field k]
    (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
    (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] : Prop :=
  Nonempty (QuasiRepCat k H₁ ≌ QuasiRepCat k H₂)

end CategoryTheory

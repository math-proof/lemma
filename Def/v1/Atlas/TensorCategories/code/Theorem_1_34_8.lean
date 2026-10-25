/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_1_34_8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.TannakaBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaBialgebra
open CategoryTheory
open TensorCategories

universe w


noncomputable section

/-- Inverse direction of Theorem 1.34.8: a finite-dimensional quasi-bialgebra
gives rise to the data of its representation category equipped with a quasi-fiber
functor. -/
noncomputable def theorem_1_34_8_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [QuasiBialgebra k H] [FiniteDimensional k H] :
    QuasiBialgebraRepData k H :=
  tannaka_reconstruction_quasi_bialgebra_inverse k H

/-- Round-trip for the category side of Theorem 1.34.8: reconstructing a
quasi-bialgebra from a category with quasi-fiber functor and then taking its
representations recovers the original category up to monoidal equivalence. -/
noncomputable def theorem_1_34_8_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    let data := tannaka_reconstruction_quasi_bialgebra_forward k C QF
    MonoidalEquiv_134 C data.RepH :=
  tannaka_reconstruction_quasi_bialgebra_roundtrip_category k C QF

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_50_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.Corollary_1_50_4
set_option maxHeartbeats 800000

universe u v


noncomputable section

/-- Allows a `SubQuasiHopfAlgebra` to be treated as a type by coercing to its underlying
subalgebra. -/
instance SubQuasiHopfAlgebra.instSort {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] :
    CoeSort (SubQuasiHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

/-- The underlying subalgebra of a quasi-Hopf subalgebra carries the natural k-module structure
inherited from H. -/
instance SubQuasiHopfAlgebra.instModuleBase {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    (K : SubQuasiHopfAlgebra k H) : Module k K := K.toSubalgebra.module'

/-- The chain of scalar actions k → K → H from a quasi-Hopf subalgebra K of H satisfies the
scalar tower axiom. -/
instance SubQuasiHopfAlgebra.instSTH {k : Type u} {H : Type v}
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    (K : SubQuasiHopfAlgebra k H) : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

end

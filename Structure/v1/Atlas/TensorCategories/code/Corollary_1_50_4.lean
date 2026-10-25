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
set_option maxHeartbeats 800000

universe u v


noncomputable section

/-- A quasi-Hopf subalgebra of a quasi-Hopf algebra H: a subalgebra of H that is stable under
the antipode S of H. -/
structure SubQuasiHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra →
    (QuasiHopfAlgebra.S (R := k) (H := H)) x ∈ toSubalgebra

end

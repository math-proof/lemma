/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
import Instance.v1.Atlas.TensorCategories.code.NicholsZoeller
set_option maxHeartbeats 800000

universe u v


noncomputable section

/-- EGNO Corollary 1.50.4: a finite-dimensional quasi-Hopf algebra `H` is free as a module
over any sub-quasi-Hopf algebra `K`. -/
class QuasiHopfFreeness (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Prop where
  free : Module.Free K H
  finite : Module.Finite K H
  finrank_dvd : Module.finrank k K ∣ Module.finrank k H

end

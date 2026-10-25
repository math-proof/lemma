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
import Class.v1.Atlas.TensorCategories.code.NicholsZoeller.Part2
set_option maxHeartbeats 800000

universe u v


noncomputable section

section QuasiHopfFreenessInstance

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H] (K : SubQuasiHopfAlgebra k H)


section NicholsZoellerHelpers

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H] (K : SubHopfAlgebra k H)

/-- Extract Nichols-Zoeller freeness from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.free : Module.Free K H :=
  NicholsZoellerFreeness.free

/-- Extract module-finiteness from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.finite : Module.Finite K H :=
  NicholsZoellerFreeness.finite

/-- Extract dimension divisibility from the `NicholsZoellerFreeness` bundle. -/
theorem NicholsZoeller.finrank_dvd :
    Module.finrank k K ∣ Module.finrank k H :=
  NicholsZoellerFreeness.finrank_dvd

end NicholsZoellerHelpers
end QuasiHopfFreenessInstance
end

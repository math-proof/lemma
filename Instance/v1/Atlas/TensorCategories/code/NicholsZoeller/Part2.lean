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
import Structure.v1.Atlas.TensorCategories.code.NicholsZoeller.Part2
set_option maxHeartbeats 800000

universe u v


noncomputable section

section QuasiHopfFreenessInstance

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H] (K : SubQuasiHopfAlgebra k H)


section SubHopfAlgebraInstances

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]

/-- Coerce a `SubHopfAlgebra` to its underlying `Subalgebra`. -/
instance SubHopfAlgebra.instCoe : CoeOut (SubHopfAlgebra k H) (Subalgebra k H) :=
  ⟨SubHopfAlgebra.toSubalgebra⟩

/-- View a `SubHopfAlgebra` as a type via its underlying subalgebra. -/
instance SubHopfAlgebra.instSort : CoeSort (SubHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

variable (K : SubHopfAlgebra k H)

/-- The base-field `k`-module structure on a sub-Hopf algebra `K`. -/
instance SubHopfAlgebra.instModuleBase : Module k K := K.toSubalgebra.module'

/-- Scalar tower `k → K → H` for a sub-Hopf algebra `K ⊆ H`. -/
instance SubHopfAlgebra.instSTH : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

/-- A sub-Hopf algebra over a field is free as a module over the base field. -/
instance SubHopfAlgebra.instFreekK : Module.Free k K :=
  Module.Free.of_divisionRing k K

/-- A sub-Hopf algebra of a nontrivial Hopf algebra over a field is itself nontrivial. -/

variable [FiniteDimensional k H]

/-- A sub-Hopf algebra of a finite-dimensional Hopf algebra is itself finite-dimensional. -/
instance SubHopfAlgebra.instFinDim : FiniteDimensional k K :=
  FiniteDimensional.finiteDimensional_submodule K.toSubalgebra.toSubmodule

end SubHopfAlgebraInstances
end QuasiHopfFreenessInstance
end

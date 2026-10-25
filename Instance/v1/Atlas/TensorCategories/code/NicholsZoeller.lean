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
import Structure.v1.Atlas.TensorCategories.code.NicholsZoeller
set_option maxHeartbeats 800000

universe u v


noncomputable section

section SubQuasiHopfAlgebraInstances

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]

/-- Coerce a `SubQuasiHopfAlgebra` to its underlying `Subalgebra`. -/
instance SubQuasiHopfAlgebra.instCoe : CoeOut (SubQuasiHopfAlgebra k H) (Subalgebra k H) :=
  ⟨SubQuasiHopfAlgebra.toSubalgebra⟩

/-- View a `SubQuasiHopfAlgebra` as a type via its underlying subalgebra. -/
instance SubQuasiHopfAlgebra.instSort : CoeSort (SubQuasiHopfAlgebra k H) (Type v) :=
  ⟨fun K => K.toSubalgebra⟩

variable (K : SubQuasiHopfAlgebra k H)

/-- The base-field `k`-module structure on a sub-quasi-Hopf algebra `K`. -/
instance SubQuasiHopfAlgebra.instModuleBase : Module k K := K.toSubalgebra.module'

/-- Scalar tower `k → K → H` for a sub-quasi-Hopf algebra `K ⊆ H`. -/
instance SubQuasiHopfAlgebra.instSTH : IsScalarTower k K H :=
  Subalgebra.isScalarTower_mid K.toSubalgebra

/-- A sub-quasi-Hopf-algebra over a field is free as a module over the base field. -/
instance SubQuasiHopfAlgebra.instFreekK : Module.Free k K :=
  Module.Free.of_divisionRing k K

/-- A quasi-Hopf algebra over a field is nontrivial. -/

variable [FiniteDimensional k H]

/-- A sub-quasi-Hopf algebra of a finite-dimensional quasi-Hopf algebra is itself
finite-dimensional. -/
instance SubQuasiHopfAlgebra.instFinDim : FiniteDimensional k K :=
  FiniteDimensional.finiteDimensional_submodule K.toSubalgebra.toSubmodule

end SubQuasiHopfAlgebraInstances
end

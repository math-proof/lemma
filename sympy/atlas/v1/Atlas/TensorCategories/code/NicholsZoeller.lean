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
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiBialgebra

set_option maxHeartbeats 800000

universe u v

noncomputable section


/-- A sub-quasi-Hopf-algebra of `H`: a `k`-subalgebra closed under the antipode. -/
structure SubQuasiHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra →
    (QuasiHopfAlgebra.S (R := k) (H := H)) x ∈ toSubalgebra

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

/-- The dimension of a sub-quasi-Hopf algebra over the base field is strictly positive. -/
end SubQuasiHopfAlgebraInstances

/-- EGNO Corollary 1.50.4: a finite-dimensional quasi-Hopf algebra `H` is free as a module
over any sub-quasi-Hopf algebra `K`. -/
class QuasiHopfFreeness (k : Type u) (H : Type v)
    [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H] [FiniteDimensional k H]
    (K : SubQuasiHopfAlgebra k H) : Prop where
  free : Module.Free K H
  finite : Module.Finite K H
  finrank_dvd : Module.finrank k K ∣ Module.finrank k H

section QuasiHopfFreenessInstance

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H] (K : SubQuasiHopfAlgebra k H)


/-- A Hopf algebra over a field is nontrivial: the counit distinguishes `0` and `1`. -/
structure SubHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra → HopfAlgebra.antipode k x ∈ toSubalgebra

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

/-- The dimension of a sub-Hopf algebra over the base field is strictly positive. -/
end SubHopfAlgebraInstances

/-- A sub-Hopf algebra of a finite-dimensional Hopf algebra satisfies the strong rank
condition. -/
class NicholsZoellerFreeness (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]
    (K : SubHopfAlgebra k H) : Prop where
  free : Module.Free K H
  finite : Module.Finite K H
  finrank_dvd : Module.finrank k K ∣ Module.finrank k H

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

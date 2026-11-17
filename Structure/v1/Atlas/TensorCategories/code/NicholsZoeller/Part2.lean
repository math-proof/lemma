/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/NicholsZoeller.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Class.v1.Atlas.TensorCategories.code.NicholsZoeller
set_option maxHeartbeats 800000

universe u v


public noncomputable section

section QuasiHopfFreenessInstance

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H] [QuasiHopfAlgebra k H]
    [FiniteDimensional k H] (K : SubQuasiHopfAlgebra k H)


/-- A Hopf algebra over a field is nontrivial: the counit distinguishes `0` and `1`. -/
structure SubHopfAlgebra (k : Type u) (H : Type v)
    [Field k] [Ring H] [HopfAlgebra k H] where
  toSubalgebra : Subalgebra k H
  antipode_mem : ∀ {x : H}, x ∈ toSubalgebra → HopfAlgebra.antipode k x ∈ toSubalgebra

end QuasiHopfFreenessInstance
end

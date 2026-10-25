/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Jacobson.Radical
set_option maxHeartbeats 800000

open TensorProduct

universe u v w


noncomputable section

example (k : Type*) [Field k] [CharZero k] (G : Type*) [CommGroup G] :
    HopfAlgebra k (MonoidAlgebra k G) := inferInstance

example (k : Type*) [Field k] [CharZero k] (G : Type*) [CommGroup G] :
    Coalgebra.IsCocomm k (MonoidAlgebra k G) := inferInstance

end

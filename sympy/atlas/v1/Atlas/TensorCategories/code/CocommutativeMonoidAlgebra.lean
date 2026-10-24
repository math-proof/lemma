/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CocommutativeMonoidAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.CartierKostant
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

/-- The monoid algebra `k[G]` of a commutative monoid `G` is a cocommutative coalgebra. -/
instance MonoidAlgebra.instIsCocommutative
    (k : Type u) (G : Type v)
    [CommSemiring k] [CommMonoid G] :
    Coalgebra.IsCocommutative k (MonoidAlgebra k G) where
  cocomm := Coalgebra.IsCocomm.comm_comp_comul

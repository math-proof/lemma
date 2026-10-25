/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part8
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- `SweedlerH4 k` is an instance of the abstract `SweedlerHopfAlgebra` axiomatisation,
witnessing that the concrete model satisfies the textbook Sweedler defining relations. -/
noncomputable instance sweedlerHopfAlgebra [CharZero k] :
    SweedlerHopfAlgebra k (SweedlerH4 k) where
  g := gen_g
  x := gen_x
  g_sq := gen_g_sq
  x_sq := gen_x_sq
  gx_comm := gen_gx_comm
  char_ne_two := two_ne_zero
  comul_g := comul_gen_g
  comul_x := comul_gen_x
  counit_g := counit_gen_g
  counit_x := counit_gen_x
  antipode_g := antipode_gen_g
  antipode_x := by rw [antipode_gen_x, gen_gx_comm]
  finrank_eq := finrank_eq

end SweedlerH4

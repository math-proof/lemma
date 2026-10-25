/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.IntegralsDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.IntegralsDefs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra Submodule
open scoped TensorProduct

universe u v


/-- One direction of Proposition 1.52.5: in a finite dimensional semisimple ring `H`, the
counit of any nonzero left integral is nonzero. -/



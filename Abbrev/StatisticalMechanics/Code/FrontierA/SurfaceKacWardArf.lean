/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

abbrev SurfaceBits (g : Nat) := Fin g → Fin 2

abbrev SurfaceHomology (g : Nat) := SurfaceBits g × SurfaceBits g

abbrev SurfaceSpinStructure (g : Nat) := SurfaceBits g × SurfaceBits g

end StatMech.FrontierA

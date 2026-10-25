/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


abbrev ons_RectVertex (M N : Nat) := ZMod (M + 1) × ZMod (N + 1)


abbrev ons_RectDart (M N : Nat) := ons_RectVertex M N × Fin 4


end StatMech.Onsager

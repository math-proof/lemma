/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open MeasureTheory TopologicalSpace


namespace StatMech

abbrev ConfigSpace (E : Type*) : Type _ := E → Bool

end StatMech

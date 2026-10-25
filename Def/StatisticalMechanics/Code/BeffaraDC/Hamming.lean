/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/Hamming.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2


namespace StatMech

namespace BeffaraDC

open ConfigSpace

variable {E : Type*} [Fintype E]


noncomputable def hammingToSet (A : Set (ConfigSpace E)) (ω : ConfigSpace E) : ℕ :=
  sInf (hammingDist ω '' A)


end BeffaraDC
end StatMech

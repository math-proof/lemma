/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Def.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part2
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetLeftHom_injective (n : Int) : Function.Injective (rlc_insetLeftHom n) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : rect (-2 * n) 0 (-n) n => (z:Site 2)) h

end
end StatMech.Universality

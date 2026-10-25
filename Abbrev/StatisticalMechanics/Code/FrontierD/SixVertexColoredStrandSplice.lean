/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev FKLayeredStrandSlot (T : EvenTorus) :=
  Bool × T.Vertex × Bool

end
end StatMech.FrontierD

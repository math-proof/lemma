/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing

open StatMech.FrontierD

#print axioms FKColoredLoopPairing.iceRule
#print axioms FKColoredLoopPairing.cType_iff_color_west_eq_east
#print axioms SixVertexCompatibleLoopPairing.toColored_arrows
#print axioms FKColoredLoopPairing.toCompatible_toColored
#print axioms fkColoredLocalPairOddCross_involutive
#print axioms fkColoredLocalPairOddCross_cTypeCount_of_odd

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexHorizontalColumnClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification

open StatMech.FrontierD

#print axioms sixVertexVerticalConstantColumnCompletion
#print axioms sixVertexHorizontalColumnSeamAllowed_both_iff_free
#print axioms sixVertexHorizontalColumnSeamAllowed_false_iff_forward
#print axioms sixVertexHorizontalColumnSeamAllowed_true_iff_backward
#print axioms sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns
#print axioms sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card

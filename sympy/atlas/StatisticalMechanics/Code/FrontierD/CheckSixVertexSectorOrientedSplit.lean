/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexSectorOrientedSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit

open StatMech.FrontierD

#print axioms sixVertexSector_forwardInterlaced_refl
#print axioms sixVertexSector_forwardInterlaced_antisymm
#print axioms sixVertexSectorTransfer_eq_forward_add_transpose
#print axioms sixVertexSectorForwardTransfer_transpose_apply

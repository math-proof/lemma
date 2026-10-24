/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckFiniteTargetTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.FiniteTargetTransport

open Set
open StatMech.FrontierA

#check finiteTargetTransport_outgoing_le_one
#check finiteTargetTransport_incoming_eq_top
#check finiteTargetTransport_image

#print axioms StatMech.FrontierA.finiteTargetTransport_outgoing_le_one
#print axioms StatMech.FrontierA.finiteTargetTransport_incoming_eq_top

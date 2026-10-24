/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckFiniteTargetMassTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.FiniteTargetMassTransport

open MeasureTheory Set
open StatMech Lattice ConfigSpace FrontierA

#check finiteTarget_massTransport_origin_null

#print axioms StatMech.FrontierA.finiteTarget_massTransport_origin_null

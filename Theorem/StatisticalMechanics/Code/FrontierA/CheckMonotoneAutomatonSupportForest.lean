/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMonotoneAutomatonSupportForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSupportForest
open StatMech FrontierA

#check gnForestData_of_protected_arms
#check coarseTcount_le_boundary_of_protected_arms

#print axioms StatMech.FrontierA.gnForestData_of_protected_arms
#print axioms StatMech.FrontierA.coarseTcount_le_boundary_of_protected_arms



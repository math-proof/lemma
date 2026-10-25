/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMultivaluedMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
open StatMech FrontierA

#check multivaluedMap_source_bound
#check multivaluedMap_weight_bound
#check multivaluedMap_probability_bound

#print axioms StatMech.FrontierA.multivaluedMap_weight_bound
#print axioms StatMech.FrontierA.multivaluedMap_probability_bound



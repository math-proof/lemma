/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMonotoneAutomatonSingleSiteStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability

open StatMech FrontierA

#check site_eq_true_of_siteCluster_infinite
#check siteCluster_raise_eq_of_infinite_of_not_mem
#check siteCluster_raiseFields_eq_of_infinite_of_avoids
#check siteCluster_zeroFields_eq_of_infinite_of_avoids

#print axioms StatMech.FrontierA.siteCluster_raise_eq_of_infinite_of_not_mem
#print axioms StatMech.FrontierA.siteCluster_raiseFields_eq_of_infinite_of_avoids
#print axioms StatMech.FrontierA.siteCluster_zeroFields_eq_of_infinite_of_avoids

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckGrahamWeightedLemmaOneFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamWeightedLemmaOneFiber

open Finset SimpleGraph
open scoped BigOperators symmDiff

#print axioms StatMech.FrontierA.grahamSourcePairComponentFiber_factor
#print axioms StatMech.FrontierA.grahamSourcePairComponentFiber_det_zero

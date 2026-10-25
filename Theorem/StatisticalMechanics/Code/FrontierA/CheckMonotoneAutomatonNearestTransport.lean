/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMonotoneAutomatonNearestTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestTransport.Part2
open Set
open StatMech Lattice Percolation FrontierA

#check pairNearestHighSet_nonempty
#check pairNearestTransport_outgoing_le_one
#check pairNearestTransport_to_zero_eq_fixed
#check pairNearestTransport_incoming_eq_top
#check pairNearestHighSet_shift
#check pairNearestHighFinset_shift
#check pairNearestTransport_diagonallyInvariant

#print axioms StatMech.FrontierA.pairNearestTransport_outgoing_le_one
#print axioms StatMech.FrontierA.pairNearestTransport_incoming_eq_top
#print axioms StatMech.FrontierA.pairNearestTransport_diagonallyInvariant



/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckMassTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.MassTransport

open MeasureTheory
open StatMech Lattice ConfigSpace FrontierA

#check IsDiagonallyInvariantTransport
#check lattice_mass_transport
#check lattice_mass_transport_infinite_receiver_null
#check lattice_mass_transport_forbidden_event_null

#print axioms StatMech.FrontierA.lattice_mass_transport
#print axioms StatMech.FrontierA.lattice_mass_transport_infinite_receiver_null

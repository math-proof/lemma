module
public import Theorem.StatisticalMechanics.Code.Universality.RSWReflectedRegion
open Function MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpoint.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


abbrev rlc_shiftedEndpointPreimage (x : Site 2) : Site 2 :=
  rlc_primalDualReflect.symm x

end Universality
end StatMech

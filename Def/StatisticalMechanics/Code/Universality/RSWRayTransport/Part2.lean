/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWRayTransport.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


noncomputable def rlc_dualReflectLatticeHom :
    hypercubicLattice 2 →g hypercubicLattice 2 where
  toFun := rlc_dualReflect
  map_rel' := fun {x y} hxy => (rlc_adj_dualReflect x y).mp hxy


end Universality
end StatMech

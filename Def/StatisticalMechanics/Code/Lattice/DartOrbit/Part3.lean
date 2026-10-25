/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

noncomputable def orbitWalkAux (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (n : ℕ) → (dartSuccGraph K).Walk a ((dartNextSub K)^[n] a)
  | 0 => SimpleGraph.Walk.nil
  | (n+1) =>
      (orbitWalkAux K a n).concat (by
        rw [Function.iterate_succ_apply']
        exact dartSuccGraph_adj_next K ((dartNextSub K)^[n] a))


end Lattice
end StatMech

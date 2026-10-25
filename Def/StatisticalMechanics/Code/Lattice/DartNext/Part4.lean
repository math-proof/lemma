/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartNext.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part3
open SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def dartNext (K : Set (Site 2)) (e : Dart) : Dart := by
  classical
  exact
    if e.head + (-rot90Fun e.dir) ∈ K then
      mkDart (e.head + (-rot90Fun e.dir)) (rot90Fun e.dir) (unitWt_rot90Fun_dir e)
    else if e.tail + (-rot90Fun e.dir) ∈ K then
      mkDart (e.tail + (-rot90Fun e.dir)) e.dir (unitWt_dir e)
    else
      mkDart e.tail (-rot90Fun e.dir) (unitWt_neg_rot90Fun_dir e)


end Lattice
end StatMech

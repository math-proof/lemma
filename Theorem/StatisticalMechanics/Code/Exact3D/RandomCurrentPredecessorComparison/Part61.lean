/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part57
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem siteParity3_adj_sub_eq_one {x y : Lattice.Site 3}
    (hxy : (Lattice.hypercubicLattice 3).Adj x y) :
    siteParity3 x - siteParity3 y = 1 := by
  rw [Lattice.hypercubicLattice_adj] at hxy
  have hsumNat : ((∑ i, (x i - y i).natAbs : ℕ) : ZMod 2) = 1 := by
    rw [hxy]
    norm_num
  have hsumAbs : (∑ i, ((x i - y i).natAbs : ZMod 2)) = 1 := by
    simpa using hsumNat
  calc
    siteParity3 x - siteParity3 y
        = (∑ i, ((x i : ZMod 2) - (y i : ZMod 2))) := by
            simp [siteParity3, Finset.sum_sub_distrib]
    _ = ∑ i, ((x i - y i : ℤ) : ZMod 2) := by
            simp [sub_eq_add_neg]
    _ = ∑ i, ((x i - y i).natAbs : ZMod 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact (ZMod.natAbs_mod_two (x i - y i)).symm
    _ = 1 := hsumAbs

set_option linter.style.longLine false in


theorem siteParity3_adj_ne {x y : Lattice.Site 3}
    (hxy : (Lattice.hypercubicLattice 3).Adj x y) :
    siteParity3 x ≠ siteParity3 y := by
  have hdiff : siteParity3 x - siteParity3 y = 1 :=
    siteParity3_adj_sub_eq_one hxy
  intro hpar
  have hzero : siteParity3 x - siteParity3 y = 0 := by
    simp [hpar]
  exact zero_ne_one (hzero.symm.trans hdiff)

end Exact3D
end StatMech

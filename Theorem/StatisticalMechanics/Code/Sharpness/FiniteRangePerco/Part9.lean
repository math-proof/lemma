/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part9
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_adj_mem_box_add (K : FiniteRangeKernel d) {N : ℕ}
    {x y : Site d} (hx : x ∈ box d N) (hxy : (frpGraph K).Adj x y) :
    y ∈ box d (N + K.range) := by
  have hz := frpGraph_adj_displacement K hxy
  rw [mem_box] at hx hz ⊢
  intro i
  have heq : y = x + (y - x) := by abel
  have hadd : (y i).natAbs ≤ (x i).natAbs + ((y - x) i).natAbs := by
    conv_lhs => rw [heq, Pi.add_apply]
    exact Int.natAbs_add_le _ _
  exact hadd.trans (Nat.add_le_add (hx i) (hz i))


theorem frp_connWithin_mono_set (K : FiniteRangeKernel d)
    (omega : ConfigSpace (Sym2 (Site d))) {S T : Set (Site d)}
    (hST : S ⊆ T) {x y : S}
    (h : ConnWithin (frpGraph K) omega S x y) :
    ConnWithin (frpGraph K) omega T
      ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
  let f : ((openSub (frpGraph K) omega).induce S) →g
      ((openSub (frpGraph K) omega).induce T) :=
    { toFun := fun z => ⟨(z : Site d), hST z.2⟩
      map_rel' := fun {a b} hab => hab }
  exact h.map f


end Sharpness
end StatMech

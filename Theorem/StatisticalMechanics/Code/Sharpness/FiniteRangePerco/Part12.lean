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
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part12
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_connWithin_univ_shift (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (omega : ConfigSpace (Sym2 (Site d)))
    (x y : Site d) :
    ConnWithin (frpGraph K) (shift g omega) Set.univ
        ⟨g • x, Set.mem_univ _⟩ ⟨g • y, Set.mem_univ _⟩ ↔
      ConnWithin (frpGraph K) omega Set.univ
        ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ := by
  constructor
  · intro h
    let f : ((openSub (frpGraph K) (shift g omega)).induce Set.univ) →g
        ((openSub (frpGraph K) omega).induce Set.univ) :=
      { toFun := fun z => ⟨g⁻¹ • (z : Site d), Set.mem_univ _⟩
        map_rel' := fun {a b} hab =>
          (frpTranslateHomInv K g omega).map_rel hab }
    convert h.map f using 1 <;> simp [f]
  · intro h
    let f : ((openSub (frpGraph K) omega).induce Set.univ) →g
        ((openSub (frpGraph K) (shift g omega)).induce Set.univ) :=
      { toFun := fun z => ⟨g • (z : Site d), Set.mem_univ _⟩
        map_rel' := fun {a b} hab => (frpTranslateHom K g omega).map_rel hab }
    exact h.map f


end Sharpness
end StatMech

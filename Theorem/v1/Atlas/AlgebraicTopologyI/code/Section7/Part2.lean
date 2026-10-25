/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section7.Part2
open ExactSequence


namespace HomologyCrossProduct

section SingularIntComplexConstruction

open AlgebraicTopologyI

/-- The integer-indexed boundary squares to zero, so the singular chains
assembled with `singularIntBoundary` form an honest chain complex over `ℤ`. -/
theorem singularIntBoundary_comp (X : Type) [TopologicalSpace X] (n : ℤ) :
    (singularIntBoundary X (n - 1)).comp (singularIntBoundary X n) = 0 := by
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
  by_cases hn : 1 ≤ n
  · by_cases hn1 : 1 ≤ n - 1
    · simp only [singularIntBoundary, hn, hn1, dite_true]
      rw [hom_cast_apply_singular X (n.toNat - 1) n.toNat ((n-1).toNat)
            (by omega) (by omega) (boundaryMap (n.toNat - 1) X) x]
      rw [hom_cast_apply_singular X ((n-1).toNat - 1) ((n-1).toNat) ((n-1-1).toNat)
            (by omega) (by omega) (boundaryMap ((n-1).toNat - 1) X)]
      simp only [cast_cast]
      rw [cast_singularChains_eq_zero X (show (n-1).toNat - 1 = (n-1-1).toNat by omega)]
      rw [cast_boundaryMap_eq X (n.toNat - 1) ((n-1).toNat - 1) (by omega)]
      exact DFunLike.congr_fun (boundaryMap_comp_boundaryMap ((n-1).toNat - 1) X) _
    · simp only [singularIntBoundary, hn1, dite_false, AddMonoidHom.zero_apply]
  · simp only [singularIntBoundary, hn, dite_false, AddMonoidHom.zero_apply, map_zero]

end SingularIntComplexConstruction
end HomologyCrossProduct

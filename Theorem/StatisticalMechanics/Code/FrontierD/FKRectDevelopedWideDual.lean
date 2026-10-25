/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideDual
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectWideExteriorOpenExtension_eq_swap_of_mem
    (n : Int) (eta : ConfigSpace (Sym2 (Site 2)))
    {e : Sym2 (Site 2)}
    (he : e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n)) :
    fkRectWideExteriorOpenExtension n eta e =
      StatMech.Universality.crf_swapConfig eta e := by
  simp [fkRectWideExteriorOpenExtension, he]


end
end StatMech.FrontierD

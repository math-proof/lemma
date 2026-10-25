/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedWideDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectWideTallFinset (n : Int) : Finset (Site 2) :=
  (rect_finite 0 n 0 (3 * n)).toFinset


def fkRectWideExteriorOpenExtension (n : Int)
    (eta : ConfigSpace (Sym2 (Site 2))) : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if e ∈ StatMech.Percolation.edgesWithinFinset
      (fkRectWideTallFinset n) then
    StatMech.Universality.crf_swapConfig eta e
  else true

end
end StatMech.FrontierD

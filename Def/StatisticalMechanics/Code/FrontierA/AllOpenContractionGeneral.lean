/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenContractionGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenBoxGeneral.Part3
import Instance.StatisticalMechanics.Code.FrontierA.AllOpenContractionGeneral
open Set SimpleGraph Finset


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}

noncomputable def bgfdQ (omega : ConfigSpace (Sym2 (Site d)))
    (L : ℕ) (x : Site d) : Site d :=
  if BgfdIndexAllOpen omega L (bgn_idx L x) then
    bgfdCentre L (bgn_idx L x)
  else x


def bgfdGraph (omega : ConfigSpace (Sym2 (Site d)))
    (L : ℕ) : SimpleGraph (Site d) where
  Adj u v := u ≠ v ∧ ∃ a b : Site d,
    bgfdQ omega L a = u ∧ bgfdQ omega L b = v ∧
      (openSubgraph d omega).Adj a b
  symm := by
    constructor
    rintro u v ⟨huv, a, b, ha, hb, hab⟩
    exact ⟨huv.symm, b, a, hb, ha, hab.symm⟩

end StatMech.FrontierA

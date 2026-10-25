/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part3
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

def AnnulusEvent (ω : ConfigSpace (Sym2 (Site 2))) (n N M : ℕ) : Prop :=
  ∃ (x : Site 2) (w : (openSubgraph 2 ω).Walk x x),
    IsAnnulusCircuit ω n N w ∧
    Separates {z | z ∈ w.support} n N ∧
    ∃ y : Site 2, y ∈ box 2 M ∧ y ∉ box 2 (M - 1) ∧ Connected 2 ω x y


def annulusEvent (n N M : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | AnnulusEvent ω n N M}

end BeffaraDC
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part6
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


theorem sctTranslatedInDoubleEquiv_adj (d n : ℕ) (y : sctBox d n)
    (a b : {z : Site d // z ∈ sctTranslatedBox d n y.1}) :
    (sctTranslatedBoxGraph d n y.1).Adj a b ↔
      ((sctBoxGraph d (2 * n)).comap
        (Subtype.val :
          {z : sctBox d (2 * n) // sctTranslatedInDouble d n y z} → sctBox d (2 * n))).Adj
        (sctTranslatedInDoubleEquiv d n y a)
        (sctTranslatedInDoubleEquiv d n y b) := by
  simp [sctTranslatedBoxGraph, sctBoxGraph, sctTranslatedInDoubleEquiv,
    SimpleGraph.comap_adj]


theorem sctTranslateEquiv_adj (d n : ℕ) (y : Site d) (a b : sctBox d n) :
    (sctBoxGraph d n).Adj a b ↔
      (sctTranslatedBoxGraph d n y).Adj
        (sctTranslateEquiv d n y a) (sctTranslateEquiv d n y b) := by
  simp only [sctBoxGraph, sctTranslatedBoxGraph, SimpleGraph.induce_adj,
    hypercubicLattice_adj]
  have hs : (∑ i, (a.1 i - b.1 i).natAbs) =
      ∑ i, (((sctTranslateEquiv d n y a).1 i) -
        ((sctTranslateEquiv d n y b).1 i)).natAbs := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change a.1 i - b.1 i = (a.1 i - y i) - (b.1 i - y i)
    ring
  rw [hs]


end Sharpness
end StatMech

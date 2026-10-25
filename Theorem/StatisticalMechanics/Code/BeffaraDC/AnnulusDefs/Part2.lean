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
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part2
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

theorem IsAnnulusCircuit.isCircuit {ω : ConfigSpace (Sym2 (Site 2))} {n N : ℕ}
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x} (h : IsAnnulusCircuit ω n N w) :
    w.IsCircuit := h.1


theorem IsAnnulusCircuit.support_subset_box {ω : ConfigSpace (Sym2 (Site 2))}
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : ∀ y ∈ w.support, y ∈ box 2 N :=
  fun y hy => (h.2 y hy).1


theorem IsAnnulusCircuit.support_avoids_inner {ω : ConfigSpace (Sym2 (Site 2))}
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : ∀ y ∈ w.support, y ∉ box 2 n :=
  fun y hy => (h.2 y hy).2


theorem IsAnnulusCircuit.base_mem {ω : ConfigSpace (Sym2 (Site 2))} {n N : ℕ}
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (h : IsAnnulusCircuit ω n N w) : x ∈ annulus n N :=
  h.2 x (Walk.start_mem_support w)


end BeffaraDC
end StatMech

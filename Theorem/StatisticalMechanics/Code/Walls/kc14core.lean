/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc14core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc13core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc14_finiteEvenComponent_disjoint_leftRegion (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ Vc.support) (hzout : z ∉ jec_leftRegion Vc) :
    Disjoint (kc12_component Vc z) (jec_leftRegion Vc) := by
  rw [Set.disjoint_left]
  intro w hwC hwIn
  exact kc13_finiteComponent_outside Vc hz hzout hwC hwIn


theorem kc14_finiteEvenComponent_second_region (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hz : z ∉ Vc.support) (hzout : z ∉ jec_leftRegion Vc)
    (hfin : (kc12_component Vc z).Finite) :
    (kc12_component Vc z).Finite ∧
    (∀ w ∈ kc12_component Vc z, w ∉ jec_leftRegion Vc) ∧
    (∀ w ∈ kc12_component Vc z, ∀ w2 : Site 2, (hypercubicLattice 2).Adj w w2 →
      w2 ∉ kc12_component Vc z → w2 ∈ Vc.support) ∧
    Disjoint (kc12_component Vc z) (jec_leftRegion Vc) :=
  ⟨hfin,
   fun _ hwC => kc13_finiteComponent_outside Vc hz hzout hwC,
   fun _ hwC _ hadj hw2notC => kc13_finiteComponent_boundary_onSupport Vc hz hwC hadj hw2notC,
   kc14_finiteEvenComponent_disjoint_leftRegion Vc hz hzout⟩


end Walls
end StatMech

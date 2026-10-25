/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part5
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_mem_leftRegion {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (z : Site 2) : z ∈ jec_leftRegion Vc ↔ ¬ Even (jec_rayCount z Vc) := Iff.rfl


theorem jec_leftRegion_bdEdge_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hu, hv⟩ := hcon
  rw [bdEdge_mk] at hbd
  simp only [jec_mem_leftRegion] at hbd
  
  have hpar := jec_localConstancy Vc hadj hu hv
  tauto


end Lattice
end StatMech

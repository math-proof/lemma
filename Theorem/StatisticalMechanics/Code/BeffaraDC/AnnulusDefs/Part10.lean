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
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

variable (D : SymmetricDomain)


@[simp]
theorem mem_connectionEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ D.connectionEvent ↔ D.Connected ω := Iff.rfl


theorem Connected.connected {D : SymmetricDomain} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : D.Connected ω) :
    ∃ x y : Site 2, x ∈ {z | z ∈ D.γ₁.support} ∧ y ∈ {z | z ∈ D.γ₂.support} ∧
      StatMech.Lattice.Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩


theorem connectionEvent_increasing {D : SymmetricDomain}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ D.connectionEvent) : ω' ∈ D.connectionEvent := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono h hxy⟩

end SymmetricDomain
end BeffaraDC
end StatMech

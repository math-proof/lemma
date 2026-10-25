/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part2
set_option linter.unusedSectionVars false


namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- A periodic flag of $\mathfrak{o}$-lattices: a $\mathbb{Z}$-indexed ascending
chain $\cdots \subset \Lambda_i \subset \Lambda_{i+1} \subset \cdots$ in
$V = k^n$, periodic with period $n$ up to scaling by $\pi$, with
one-dimensional consecutive quotients. -/
structure PeriodicFlag where
  lattice : ℤ → DVRContext.OLattice C
  ascending : ∀ i : ℤ, (lattice i).carrier ⊆ (lattice (i + 1)).carrier
  periodic : ∀ i : ℤ,
    (lattice (i + C.n)).carrier =
      {v | ∃ w ∈ (lattice i).carrier, v = C.oscal C.uniformizer w}
  quotient_annihilated : ∀ i : ℤ,
    ∀ v ∈ (lattice (i + 1)).carrier,
      C.oscal C.uniformizer v ∈ (lattice i).carrier
  quotient_one_dim : ∀ i : ℤ,
    ∃ w ∈ (lattice (i + 1)).carrier,
      w ∉ (lattice i).carrier ∧
      ∀ v ∈ (lattice (i + 1)).carrier, ∃ r : C.𝔬,
        (fun j => v j - C.embed r * w j) ∈ (lattice i).carrier

end AffineBuildingSLV

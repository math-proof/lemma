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
import Structure.v1.Atlas.Buildings.code.Building.AffineSLV
set_option linter.unusedSectionVars false


namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- A lattice $\Lambda$ is decomposable with respect to a frame
$F = (L_1, \ldots, L_n)$ if $\Lambda = \bigoplus_j s_j \mathfrak{o} v_j$ for
some scalars $s_j \in k^\times$ and chosen generators $v_j$ of the lines. -/
def IsDecomposableWrtFrame (F : Frame C) (Λ : DVRContext.OLattice C) : Prop :=
  ∃ scales : Fin C.n → C.k,
    (∀ j, scales j ≠ 0) ∧
    Λ.carrier = {v | ∃ c : Fin C.n → C.𝔬,
      v = fun i => ∑ j, C.embed (c j) * scales j * (F.lines j).generator i}

/-- The apartment $A_F$ associated to a frame $F$: the set of simplices all of
whose vertices are classes of frame-decomposable lattices. -/
def Apartment (F : Frame C) : Set (Simplex C) :=
  {σ | ∀ ξ ∈ σ.vertices,
    ∃ Λ : DVRContext.OLattice C,
      Quot.mk _ Λ = ξ ∧ IsDecomposableWrtFrame C F Λ}

end AffineBuildingSLV

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

theorem ons_optionAnchoredEquiv_apply_vertexOfSite
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool) (x : Site d) :
    (ons_optionAnchoredEquiv tau).1 (ons_plusWiredVertexOfSite d n x) =
      !(glue (plusField d) tau x) := by
  by_cases hx : x ∈ box d n
  · simp [ons_plusWiredVertexOfSite, hx, glue, ons_optionAnchoredEquiv]
  · simp [ons_plusWiredVertexOfSite, hx, glue, plusField,
      ons_optionAnchoredEquiv]


theorem mem_plusWiredCut_iff
    (d n : Nat) (tau : {x // x ∈ box d n} → Bool)
    (edge : ons_PlusWiredBond d n) :
    edge ∈ multibondCut (ons_plusWiredBondEnds d n)
        (ons_optionAnchoredEquiv tau).1 ↔
      edge.1 ∈ ons_fvCutEdges (bondFinsetTouch d n)
        (glue (plusField d) tau) := by
  rw [mem_multibondCut]
  change
    (ons_optionAnchoredEquiv tau).1
        (ons_plusWiredVertexOfSite d n edge.1.out.1) ≠
      (ons_optionAnchoredEquiv tau).1
        (ons_plusWiredVertexOfSite d n edge.1.out.2) ↔ _
  rw [ons_optionAnchoredEquiv_apply_vertexOfSite,
    ons_optionAnchoredEquiv_apply_vertexOfSite]
  unfold ons_fvCutEdges
  rw [Finset.mem_filter]
  simp only [edge.2, true_and]
  rw [← kwg_isSplit_iff_bond_neg]
  have hout : s(edge.1.out.1, edge.1.out.2) = edge.1 := by
    change Sym2.mk edge.1.out.1 edge.1.out.2 = edge.1
    rw [Sym2.mk, edge.1.out_eq]
  have hsplit : kwg_isSplit (glue (plusField d) tau) edge.1 ↔
      glue (plusField d) tau edge.1.out.1 ≠
        glue (plusField d) tau edge.1.out.2 := by
    calc
      kwg_isSplit (glue (plusField d) tau) edge.1 ↔
          kwg_isSplit (glue (plusField d) tau)
            s(edge.1.out.1, edge.1.out.2) := by rw [hout]
      _ ↔ _ := kwg_isSplit_mk _ _ _
  rw [hsplit]
  cases glue (plusField d) tau edge.1.out.1 <;>
    cases glue (plusField d) tau edge.1.out.2 <;> simp


end
end StatMech.Onsager

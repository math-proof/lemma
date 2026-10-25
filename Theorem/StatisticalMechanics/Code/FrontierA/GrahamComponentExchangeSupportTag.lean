/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeSupportTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

theorem componentExchange_zeroComponent_source_empty
    {ends : I → Sym2 W} {m K : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag) (hKm : K ⊆ m)
    (hjk : j ≠ k)
    (hleft : LeftRowSupport ends m j k l zero K) :
    sources ends (edgeComponent ends K zero) = ∅ := by
  have hjkConn : connK ends K j k :=
    StatMech.Walls.gc6_pairingPath_abstract ends K K
      (fun i hi => hloop i (hKm hi)) Finset.Subset.rfl hleft.1 hjk
  rw [sources_edgeComponent, hleft.1]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rcases Finset.mem_inter.mp hx with ⟨hx, hcomp⟩
  rw [mem_compOf] at hcomp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hleft.2.2.1
      (connK_symm ends K (hcomp.trans hjkConn))
  · exact hleft.2.2.1 (connK_symm ends K hcomp)


end StatMech.GrahamGHS.FourColor

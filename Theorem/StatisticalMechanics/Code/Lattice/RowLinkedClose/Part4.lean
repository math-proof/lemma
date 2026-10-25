/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Def.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rlc_downLink_of_leftEndDescends {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_LeftEndDescends Vc seed M) :
    rlc_DownLink Vc seed M := by
  intro z hz hzs
  by_cases hleft : (![z 0 - 1, z 1] : Site 2) ∈ Vc.support
  · exact hres z hz hzs hleft
  · have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq] at hz hleft ⊢
    have hl : (![(![z 0, z 1] : Site 2) 0 - 1, (![z 0, z 1] : Site 2) 1] : Site 2)
        ∉ Vc.support := by
      simpa using hleft
    exact rlc_descend_via_leftStep Vc M hMb hz hl


theorem rlc_rowLinked_of_downLink {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : rlc_DownLink Vc seed M) :
    jil_RowLinked Vc seed := by
  have key : ∀ n : ℕ, ∀ z ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z = n →
      ∃ p : (hypercubicLattice 2).Walk z seed, ∀ w ∈ p.support, w ∉ Vc.support := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hz hn
      by_cases hzs : z = seed
      · cases hzs
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro w hw
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        cases hw
        exact (jil_mem_offSupportInterior Vc seed |>.mp hz).1
      · obtain ⟨z', hz', hlt, p, hp⟩ := hdl z hz hzs
        rw [hn] at hlt
        obtain ⟨q, hq⟩ := ih (rlc_lexMeasure M z') hlt z' hz' rfl
        refine ⟨p.append q, ?_⟩
        intro w hw
        rw [SimpleGraph.Walk.support_append, List.mem_append] at hw
        rcases hw with h | h
        · exact hp w h
        · exact hq w (List.mem_of_mem_tail h)
  intro z hz
  exact key (rlc_lexMeasure M z) z hz rfl


theorem rlc_rowLinked_of_leftEndDescends {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_LeftEndDescends Vc seed M) :
    jil_RowLinked Vc seed :=
  rlc_rowLinked_of_downLink Vc M (rlc_downLink_of_leftEndDescends Vc M hMb hres)


end Lattice
end StatMech

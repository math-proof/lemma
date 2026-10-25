/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part30


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    (∑ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component) = 2 := by
  classical
  unfold sixVertexDegreeTwoSynchronizedComponentCharge
  rw [Finset.sum_comm]
  simp_rw [Fintype.sum_ite_eq]
  have htotal := sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle
  rw [← htotal]
  apply Finset.sum_congr
  · ext d
    simp
  · intro d hd
    rfl

theorem sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoSynchronizedTotalComponentCharge homega heta hdegree =
      2 := by
  unfold sixVertexDegreeTwoSynchronizedTotalComponentCharge
  exact sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle


theorem sixVertexDegreeTwoSynchronizedComponent_predecessors_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
        component ↔
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
          (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) =
        component := by
  have hreach := sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable
    homega heta hdegree d
  have heq : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) =
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk
        (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) :=
    ConnectedComponent.sound hreach
  rw [heq]


theorem sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∃ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component = 1) \/
      (∀ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≠ 1) := by
  classical
  by_cases h : ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
    sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
      component = 1
  · exact Or.inl h
  · exact Or.inr (by
      intro component hone
      exact h ⟨component, hone⟩)


theorem sixVertexDegreeTwoSynchronizedComponent_halfFlow_charge_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    (∑ component :
        (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      (sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component : ℚ) * (1 / 2)) = 1 := by
  rw [← Finset.sum_mul]
  rw [← Int.cast_sum]
  rw [sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle]
  norm_num


theorem exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hle : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 1) :
    ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component = 1 := by
  classical
  by_contra hnone
  have hnonpos : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 0 := by
    intro component
    have hne : sixVertexDegreeTwoSynchronizedComponentCharge homega heta
        hdegree component ≠ 1 := by
      intro hone
      exact hnone ⟨component, hone⟩
    have hbound := hle component
    omega
  have hsumNonpos : sixVertexDegreeTwoSynchronizedTotalComponentCharge homega
      heta hdegree ≤ 0 := by
    unfold sixVertexDegreeTwoSynchronizedTotalComponentCharge
    exact Finset.sum_nonpos (fun component _ => hnonpos component)
  rw [sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two homega heta
    hdegree middle homegaSector hetaSector hmiddle] at hsumNonpos
  omega


theorem exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hnoUnit : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≠ 1) :
    ∃ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component := by
  classical
  by_contra hnone
  have hleOne : ∀ component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent,
      sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree
        component ≤ 1 := by
    intro component
    have hnot : ¬ 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega
        heta hdegree component := by
      intro htwo
      exact hnone ⟨component, htwo⟩
    omega
  obtain ⟨component, hone⟩ :=
    exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one
      homega heta hdegree middle homegaSector hetaSector hmiddle hleOne
  exact hnoUnit component hone


end
end StatMech.FrontierD

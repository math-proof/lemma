/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexArrowsComplement_horizontal
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).horizontal v = !omega.horizontal v := rfl

@[simp] theorem sixVertexArrowsComplement_vertical
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).vertical v = !omega.vertical v := rfl

@[simp] theorem sixVertexArrowsComplement_complement
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexArrowsComplement (sixVertexArrowsComplement omega) = omega := by
  ext v <;> simp [sixVertexArrowsComplement]

theorem sixVertexArrowsComplement_injective {T : EvenTorus} :
    Function.Injective (@sixVertexArrowsComplement T) := by
  intro first second heq
  have h := congrArg sixVertexArrowsComplement heq
  simpa using h

theorem sixVertexArrowsComplement_iceRule
    {T : EvenTorus} {omega : SixVertexArrows T}
    (homega : omega.IceRule) :
    (sixVertexArrowsComplement omega).IceRule := by
  intro v
  have h := homega v
  unfold SixVertexArrows.incomingCount at h ⊢
  simp only [sixVertexArrowsComplement_horizontal,
    sixVertexArrowsComplement_vertical, Bool.not_not]
  generalize omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = west at h ⊢
  generalize omega.horizontal v = east at h ⊢
  generalize omega.vertical
      (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = south at h ⊢
  generalize omega.vertical v = north at h ⊢
  cases west <;> cases east <;> cases south <;> cases north <;> simp_all

theorem sixVertexArrowsComplement_isCType_iff
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexArrowsComplement omega).IsCType v ↔ omega.IsCType v := by
  unfold SixVertexArrows.IsCType
  simp only [sixVertexArrowsComplement_horizontal, Bool.not_not]
  generalize omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = west
  generalize omega.horizontal v = east
  cases west <;> cases east <;> decide +revert

@[simp] theorem sixVertexArrowsComplement_cTypeCount
    {T : EvenTorus} (omega : SixVertexArrows T) :
    sixVertexTorusCTypeCount (sixVertexArrowsComplement omega) =
      sixVertexTorusCTypeCount omega := by
  classical
  unfold sixVertexTorusCTypeCount
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : omega.IsCType v
  · simp [h, (sixVertexArrowsComplement_isCType_iff omega v).2 h]
  · have hc : ¬ (sixVertexArrowsComplement omega).IsCType v :=
      fun hc => h ((sixVertexArrowsComplement_isCType_iff omega v).1 hc)
    simp [h, hc]

theorem sixVertexUpCount_complement {N : Nat} (row : SixVertexRow N) :
    sixVertexUpCount (fun i => !row i) = N - sixVertexUpCount row := by
  unfold sixVertexUpCount
  have hset : ({i | !row i} : Finset (Fin N)) =
      ({i | row i} : Finset (Fin N))ᶜ := by
    ext i
    cases row i <;> simp
  rw [hset, Finset.card_compl]
  simp

end
end StatMech.FrontierD

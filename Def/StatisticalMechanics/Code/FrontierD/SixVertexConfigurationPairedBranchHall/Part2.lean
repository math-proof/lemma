/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPairedBranchGeometricConstruction.toEmbeddings
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (geometric : SixVertexConfigurationPairedBranchGeometricConstruction
      T middle hmiddle_pos hmiddle_lt grade) :
    SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade where
  branch choice :=
    ⟨fun source => geometric.target source choice,
      fun _ _ heq => geometric.recoverable choice _ _ heq⟩
  distinct := geometric.distinct


def SixVertexConfigurationPairedBranchRelated
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade)
    (target : SixVertexConfigurationPairBigradeFiber T middle middle grade) :
    Prop :=
  exists branch, embeddings.branch branch source = target

def SixVertexConfigurationPairedBranchEmbeddings.sourceCertificates
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (embeddings : SixVertexConfigurationPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexConfigurationPairBigradeFiber T
      (sixVertexConfigurationLowerSector middle hmiddle_pos)
      (sixVertexConfigurationUpperSector middle hmiddle_lt) grade) :
    Fin 2 ↪
      {target : SixVertexConfigurationPairBigradeFiber T middle middle grade //
        SixVertexConfigurationPairedBranchRelated
          embeddings source target} where
  toFun branch :=
    ⟨embeddings.branch (finTwoEquiv branch) source,
      ⟨finTwoEquiv branch, rfl⟩⟩
  inj' := by
    intro first second heq
    apply finTwoEquiv.injective
    cases hfirst : finTwoEquiv first <;>
      cases hsecond : finTwoEquiv second
    · rfl
    · exfalso
      exact embeddings.distinct source (by
        simpa [hfirst, hsecond] using congrArg Subtype.val heq)
    · exfalso
      exact embeddings.distinct source (by
        simpa [hfirst, hsecond] using (congrArg Subtype.val heq).symm)
    · rfl

end
end StatMech.FrontierD

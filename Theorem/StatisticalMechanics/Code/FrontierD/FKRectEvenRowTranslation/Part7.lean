/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part7
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectConnectedWithin_evenRowTranslation_iff
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega)
        (fkRectEvenRowTranslationSet R s S)
        (fkRectEvenRowTranslationSetEquiv R s S x)
        (fkRectEvenRowTranslationSetEquiv R s S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphEvenRowTranslationInduceIso
    R s hs omega S).reachable_iff


theorem fkRectCritical_connectedWithinMass_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectEvenRowTranslationSet R s S)
          (fkRectEvenRowTranslationSetEquiv R s S x)
          (fkRectEvenRowTranslationSetEquiv R s S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectEvenRowTranslationConfigurationEquiv R s
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectEvenRowTranslationSet R s S)
      (fkRectEvenRowTranslationSetEquiv R s S x)
      (fkRectEvenRowTranslationSetEquiv R s S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_evenRowTranslation_iff
      R s hs omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_evenRowTranslation
      R s hs q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]

end
end StatMech.FrontierD

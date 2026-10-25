/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedEndpointReflectionGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideEndpoint.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedEndpointReflectionGlue
open Set


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem fkRectConnectedWithin_developedReflection_iff
    (R : FKRectTorus) (center : Nat) (omega : R.Configuration)
    (S : Set R.Vertex) (x y : S) :
    FKRectConnectedWithin R
        (fkRectDevelopedReflectionConfigurationEquiv R center omega)
        (fkRectDevelopedReflectionSet R center S)
        (fkRectDevelopedReflectionSetEquiv R center S x)
        (fkRectDevelopedReflectionSetEquiv R center S y) ↔
      FKRectConnectedWithin R omega S x y := by
  exact (fkRectOpenGraphDevelopedReflectionInduceIso
    R center omega S).reachable_iff


theorem fkRectCritical_connectedWithinMass_developedReflection
    (R : FKRectTorus) (center : Nat) (q : Real)
    (S : Set R.Vertex) (x y : S) :
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectDevelopedReflectionSet R center S)
          (fkRectDevelopedReflectionSetEquiv R center S x)
          (fkRectDevelopedReflectionSetEquiv R center S y)} =
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  classical
  let C := fkRectDevelopedReflectionConfigurationEquiv R center
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega
      (fkRectDevelopedReflectionSet R center S)
      (fkRectDevelopedReflectionSetEquiv R center S x)
      (fkRectDevelopedReflectionSetEquiv R center S y)}
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    B.indicator (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ B ↔ omega ∈ A :=
    fkRectConnectedWithin_developedReflection_iff
      R center omega S x y
  have hprob : fkRectCriticalRandomClusterProb R q (C omega) =
      fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_developedReflection
      R center q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun hB => hA (hmem.mp hB))]


theorem fkRectCritical_connectedWithinMass_sq_le_reflectedUnion
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Set R.Vertex) (x y : S) :
    let center := y.1.2.val
    let Sr := fkRectDevelopedReflectionSet R center S
    let xr := fkRectDevelopedReflectionVertexEquiv R center x.1
    fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} ^ 2 ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega (S ∪ Sr)
          ⟨x.1, Or.inl x.2⟩ ⟨xr, Or.inr ⟨x.1, x.2, rfl⟩⟩} := by
  dsimp only
  let center := y.1.2.val
  let Sr := fkRectDevelopedReflectionSet R center S
  let xrS : Sr := fkRectDevelopedReflectionSetEquiv R center S x
  let yrS : Sr := fkRectDevelopedReflectionSetEquiv R center S y
  let A : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega Sr yrS xrS}
  have hA : IsIncreasing A :=
    fkRectConnectedWithin_isIncreasing R S x y
  have hB : IsIncreasing B :=
    fkRectConnectedWithin_isIncreasing R Sr yrS xrS
  have hmass : fkRectCriticalEventMass R q B =
      fkRectCriticalEventMass R q A := by
    calc
      fkRectCriticalEventMass R q B =
          fkRectCriticalEventMass R q
            {omega | FKRectConnectedWithin R omega Sr xrS yrS} := by
        congr 1
        ext omega
        exact SimpleGraph.reachable_comm
      _ = fkRectCriticalEventMass R q A := by
        simpa [A, Sr, xrS, yrS, center] using
          (fkRectCritical_connectedWithinMass_developedReflection
            R center q S x y)
  have hinter : A ∩ B ⊆
      {omega | FKRectConnectedWithin R omega (S ∪ Sr)
        ⟨x.1, Or.inl x.2⟩
        ⟨xrS.1, Or.inr xrS.2⟩} := by
    intro omega homega
    have hySr : y.1 ∈ Sr := by
      refine ⟨y.1, y.2, ?_⟩
      exact fkRectDevelopedReflectionVertexEquiv_center R y.1
    have hyr : yrS = (⟨y.1, hySr⟩ : Sr) := by
      apply Subtype.ext
      exact fkRectDevelopedReflectionVertexEquiv_center R y.1
    have hBomega : FKRectConnectedWithin R omega Sr
        (⟨y.1, hySr⟩ : Sr) xrS := by
      have hBo := homega.2
      change FKRectConnectedWithin R omega Sr yrS xrS at hBo
      rwa [hyr] at hBo
    apply FKRectConnectedWithin.trans_union R omega
      x.2 y.2 hySr xrS.2 homega.1 hBomega
  calc
    fkRectCriticalEventMass R q A ^ 2 =
        fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B := by rw [hmass, pow_two]
    _ ≤ fkRectCriticalEventMass R q (A ∩ B) :=
      fkRectCriticalEventMass_mul_le_inter R hq hA hB
    _ ≤ fkRectCriticalEventMass R q
          {omega | FKRectConnectedWithin R omega (S ∪ Sr)
            ⟨x.1, Or.inl x.2⟩ ⟨xrS.1, Or.inr xrS.2⟩} :=
      fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq) hinter


theorem fkRectCritical_connectionMass_sq_le_centeredReflectionConnectionMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (x y : R.Vertex) :
    fkRectCriticalEventMass R q (fkRectTorusConnectionEvent R x y) ^ 2 ≤
      fkRectCriticalEventMass R q
        (fkRectTorusConnectionEvent R x
          (fkRectDevelopedReflectionVertexEquiv R y.2.val x)) := by
  let A := fkRectTorusConnectionEvent R x y
  let xr := fkRectDevelopedReflectionVertexEquiv R y.2.val x
  let B := fkRectTorusConnectionEvent R y xr
  have hA : IsIncreasing A :=
    fkRectTorusConnectionEvent_isIncreasing R x y
  have hB : IsIncreasing B :=
    fkRectTorusConnectionEvent_isIncreasing R y xr
  have hmass : fkRectCriticalEventMass R q B =
      fkRectCriticalEventMass R q A := by
    calc
      fkRectCriticalEventMass R q B =
          fkRectCriticalEventMass R q
            (fkRectTorusConnectionEvent R xr y) := by
        congr 1
        ext omega
        exact SimpleGraph.reachable_comm
      _ = fkRectCriticalEventMass R q A := by
        simpa [A, xr] using
          (fkRectCritical_connectionMass_developedReflection
            R y.2.val q x y)
  have hinter : A ∩ B ⊆ fkRectTorusConnectionEvent R x xr := by
    intro omega homega
    exact homega.1.trans homega.2
  calc
    fkRectCriticalEventMass R q A ^ 2 =
        fkRectCriticalEventMass R q A *
          fkRectCriticalEventMass R q B := by rw [hmass, pow_two]
    _ ≤ fkRectCriticalEventMass R q (A ∩ B) :=
      fkRectCriticalEventMass_mul_le_inter R hq hA hB
    _ ≤ fkRectCriticalEventMass R q
          (fkRectTorusConnectionEvent R x xr) :=
      fkRectCriticalEventMass_mono R (zero_lt_one.trans_le hq) hinter

@[simp] theorem fkRectDevelopedReflectionVertexEquiv_fst
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    (fkRectDevelopedReflectionVertexEquiv R center v).1 = v.1 :=
  rfl


end
end StatMech.FrontierD

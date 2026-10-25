/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexBetheContinuationProjectionOn
    {a b : Real} {N n : Nat}
    (C : Set (SixVertexBetheContinuationSpace a b N n)) :
    Continuous (sixVertexBetheContinuationProjectionOn C) :=
  continuous_sixVertexBetheContinuationProjection.comp continuous_subtype_val


theorem isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian
    {a b : Real} (ha : 2 < a) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n)) (hC : IsOpen C)
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2)) :
    IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
  have hOn :=
    isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_rootJacobian
      ha hN hhalf C hjac
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  have hsub : IsLocalHomeomorphOn
      (Subtype.val : C → SixVertexBetheContinuationSpace a b N n)
      Set.univ :=
    hC.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp := hOn.comp hsub (fun q _ => q.2)
  simpa [sixVertexBetheContinuationProjectionOn, Function.comp_def] using hcomp


theorem exists_sixVertexContinuousBetheBranch_of_compactComponent
    {a b c₀ : Real} (hab : a ≤ b) (hc₀ : c₀ ∈ Set.Icc a b)
    {N n : Nat} (hN : 0 < N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hcompact : IsCompact C)
    (hlocal : IsLocalHomeomorph
      (sixVertexBetheContinuationProjectionOn C))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  have hproj : Continuous (sixVertexBetheContinuationProjectionOn C) :=
    continuous_sixVertexBetheContinuationProjectionOn C
  have hcovOn : IsCoveringMapOn
      (sixVertexBetheContinuationProjectionOn C) Set.univ :=
    IsCoveringMapOn.of_openPartialHomeomorph hproj
      (fun e _ => by
        obtain ⟨phi, he, hphi⟩ := hlocal e
        exact ⟨phi, he, hphi.symm⟩)
  have hcov : IsCoveringMap (sixVertexBetheContinuationProjectionOn C) :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  let clamp : Real → Set.Icc a b := fun t =>
    ⟨min b (max a t),
      ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩⟩
  have hclamp : Continuous clamp :=
    Continuous.subtype_mk (by fun_prop) _
  let f : C(Real, Set.Icc a b) := ⟨clamp, hclamp⟩
  have hf₀ : f c₀ = sixVertexBetheContinuationProjectionOn C z₀ := by
    rw [hz₀]
    apply Subtype.ext
    simp [f, clamp, max_eq_right hc₀.1, min_eq_right hc₀.2]
  letI : ContractibleSpace Real :=
    (contractible_iff_id_nullhomotopic Real).mpr
      ⟨0, ⟨ContinuousMap.Homotopy.affine
        (ContinuousMap.id Real) (ContinuousMap.const Real 0)⟩⟩
  obtain ⟨F, hF₀, hFlift⟩ :=
    (hcov.existsUnique_continuousMap_lifts f c₀ z₀ hf₀.symm).exists
  let roots : C(Real, Fin n → Real) :=
    ⟨fun t => (F t).1.1.2,
      continuous_subtype_val.snd.comp
        (continuous_subtype_val.comp F.continuous)⟩
  refine ⟨roots, ?_, ?_⟩
  · change (F c₀).1.1.2 = z₀.1.1.2
    rw [hF₀]
  · intro t ht
    have hprojF := congrFun hFlift t
    have hclamp_t : f t = ⟨t, ht⟩ := by
      apply Subtype.ext
      simp [f, clamp, max_eq_right ht.1, min_eq_right ht.2]
    have hfirst : (F t).1.1.1 = t := by
      have h := congrArg Subtype.val hprojF
      simpa [hclamp_t, sixVertexBetheContinuationProjectionOn,
        sixVertexBetheContinuationProjection] using h
    have hmem := (F t).1.2
    have hfix : sixVertexBetheUpdate t N n (F t).1.1.2 =
        (F t).1.1.2 := by
      calc
        sixVertexBetheUpdate t N n (F t).1.1.2 =
            sixVertexBetheUpdate (F t).1.1.1 N n (F t).1.1.2 := by
          exact congrArg
            (fun s => sixVertexBetheUpdate s N n (F t).1.1.2) hfirst.symm
        _ = (F t).1.1.2 := hmem.2.2
    exact (sixVertexBetheUpdate_eq_self_iff hN _).mp hfix


theorem exists_sixVertexContinuousBetheBranch_of_regularComponent
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (C : Set (SixVertexBetheContinuationSpace a b N n))
    (hCopen : IsOpen C) (hCcompact : IsCompact C)
    (hjac : ∀ q ∈ C,
      Function.Injective (sixVertexBetheRootJacobian N n q.1.1 q.1.2))
    (z₀ : C)
    (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) :=
  exists_sixVertexContinuousBetheBranch_of_compactComponent hab hc₀ hN C
    hCcompact
    (isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_rootJacobian
      ha hN hhalf C hCopen hjac)
    z₀ hz₀


theorem exists_sixVertexContinuousBetheBranch_of_rootJacobian
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N n : Nat} (hN : 0 < N)
    (hhalf : 2 * n ≤ N)
    (hjac : ∀ q ∈ sixVertexBetheContinuationSet a b N n,
      Function.Injective (sixVertexBetheRootJacobian N n q.1 q.2))
    (z₀ : SixVertexBetheContinuationSpace a b N n)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin n → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N n (roots t) :=
  exists_sixVertexContinuousBetheBranch_of_isLocalHomeomorph
    ha hab hc₀ hN
      (isLocalHomeomorph_sixVertexBetheContinuationProjection_of_rootJacobian
        ha hN hhalf hjac)
    z₀ hz₀

end
end StatMech.FrontierD

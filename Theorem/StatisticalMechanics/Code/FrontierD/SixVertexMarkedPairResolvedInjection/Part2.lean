/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection.Part2


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexExplicitMarkedDecoratedPair_eq_compact
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    Fintype.card
        (SixVertexExplicitMarkedDecoratedPair T left right k) =
      Fintype.card (SixVertexMarkedDecoratedPair T left right k) :=
  Fintype.card_congr
    (sixVertexExplicitMarkedDecoratedPairEquiv T left right k)


theorem card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection
    {T : EvenTorus} {sourceLeft sourceRight targetLeft targetRight :
      Fin (T.width + 1)} {k : Nat}
    (matching : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k ->
      SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
    (hinjective : Function.Injective matching) :
    Fintype.card
        (SixVertexMarkedDecoratedPair T sourceLeft sourceRight k) <=
      Fintype.card
        (SixVertexMarkedDecoratedPair T targetLeft targetRight k) := by
  have hresolved := Fintype.card_le_of_injective matching hinjective
  rw [card_sixVertexExplicitResolvedMarkedPair,
    card_sixVertexExplicitResolvedMarkedPair,
    card_sixVertexExplicitMarkedDecoratedPair_eq_compact,
    card_sixVertexExplicitMarkedDecoratedPair_eq_compact] at hresolved
  exact Nat.le_of_mul_le_mul_right hresolved (pow_pos (by norm_num) k)


theorem sixVertexMarkedSectorPairMass_le_of_resolvedInjection
    {T : EvenTorus} {sourceLeft sourceRight targetLeft targetRight :
      Fin (T.width + 1)} {k : Nat}
    (matching : SixVertexExplicitResolvedMarkedPair
        T sourceLeft sourceRight k ->
      SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
    (hinjective : Function.Injective matching) :
    sixVertexMarkedSectorPairMass T sourceLeft sourceRight k <=
      sixVertexMarkedSectorPairMass T targetLeft targetRight k := by
  have hcard := card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection
    matching hinjective
  have hcardReal :
      (Fintype.card
          (SixVertexMarkedDecoratedPair T sourceLeft sourceRight k) : Real) <=
        Fintype.card
          (SixVertexMarkedDecoratedPair T targetLeft targetRight k) := by
    exact_mod_cast hcard
  simpa only [card_sixVertexMarkedDecoratedPair_eq_pairMass] using hcardReal


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (matching : forall k : Nat,
      SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩
          ⟨middle.val + 1, by omega⟩ k ->
        SixVertexExplicitResolvedMarkedPair T middle middle k)
    (hinjective : forall k, Function.Injective (matching k)) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  intro k
  unfold sixVertexMarkedTraceLogConcavityDifference
  rw [Polynomial.coeff_sub]
  apply sub_nonneg.mpr
  have hmass := sixVertexMarkedSectorPairMass_le_of_resolvedInjection
    (matching k) (hinjective k)
  simpa only [sixVertexMarkedSectorPairMass_eq_coeff,
    Fin.val_mk, pow_two] using hmass


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hfiber : SixVertexExplicitResolvedBigradeFiberDominates T
      ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩
      middle middle) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  let witness (k : Nat) :=
    (exists_injective_bigradePreserving_iff_fiberCard
      (fun source : SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k =>
        sixVertexExplicitResolvedBigrade source)
      (fun target : SixVertexExplicitResolvedMarkedPair T middle middle k =>
        sixVertexExplicitResolvedBigrade target)).2 (fun grade => by
          simpa only [Nat.card_eq_fintype_card] using hfiber k grade)
  let matching (k : Nat) :
      SixVertexExplicitResolvedMarkedPair T
          ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k ->
        SixVertexExplicitResolvedMarkedPair T middle middle k :=
    Classical.choose (witness k)
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections
    T middle hmiddle_pos hmiddle_lt matching
  intro k
  exact (Classical.choose_spec (witness k)).1

end
end StatMech.FrontierD

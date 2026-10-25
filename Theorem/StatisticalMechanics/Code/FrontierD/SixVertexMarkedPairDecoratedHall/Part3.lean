/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedDecoratedPairHall_of_bidegree
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    (related : SixVertexMarkedDecoratedPair T lower upper k ->
      SixVertexMarkedDecoratedPair T middle middle k -> Prop)
    (degree : Nat) (hdegree : 0 < degree)
    (hsource : forall source,
      degree <= (Finset.univ.filter (related source)).card)
    (htarget : forall target,
      (Finset.univ.filter fun source => related source target).card <= degree) :
    SixVertexMarkedDecoratedPairHall
      T lower middle upper k related :=
  finiteRelationHall_of_bidegree related degree hdegree hsource htarget


theorem sixVertexMarkedDecoratedPairHall_iff_exists_injective
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) (k : Nat)
    (related : SixVertexMarkedDecoratedPair T lower upper k ->
      SixVertexMarkedDecoratedPair T middle middle k -> Prop) :
    SixVertexMarkedDecoratedPairHall T lower middle upper k related <->
      exists matching : SixVertexMarkedDecoratedPair T lower upper k ->
          SixVertexMarkedDecoratedPair T middle middle k,
        Function.Injective matching /\
          forall source, related source (matching source) := by
  unfold SixVertexMarkedDecoratedPairHall
  exact Fintype.all_card_le_filter_rel_iff_exists_injective related


theorem sixVertexMarkedSectorPairMass_le_of_decoratedHall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedDecoratedPair T lower upper k ->
      SixVertexMarkedDecoratedPair T middle middle k -> Prop}
    (hall : SixVertexMarkedDecoratedPairHall
      T lower middle upper k related) :
    sixVertexMarkedSectorPairMass T lower upper k <=
      sixVertexMarkedSectorPairMass T middle middle k := by
  obtain ⟨matching, hinjective, hrelated⟩ :=
    (sixVertexMarkedDecoratedPairHall_iff_exists_injective
      T lower middle upper k related).mp hall
  have hcard :
      Fintype.card (SixVertexMarkedDecoratedPair T lower upper k) <=
        Fintype.card (SixVertexMarkedDecoratedPair T middle middle k) :=
    Fintype.card_le_of_injective matching hinjective
  have hcardReal :
      (Fintype.card
          (SixVertexMarkedDecoratedPair T lower upper k) : Real) <=
        Fintype.card
          (SixVertexMarkedDecoratedPair T middle middle k) := by
    exact_mod_cast hcard
  rw [card_sixVertexMarkedDecoratedPair_eq_pairMass,
    card_sixVertexMarkedDecoratedPair_eq_pairMass] at hcardReal
  exact hcardReal


theorem coeff_shiftedSectorTrace_mul_le_sq_of_decoratedHall
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)} {k : Nat}
    {related : SixVertexMarkedDecoratedPair T lower upper k ->
      SixVertexMarkedDecoratedPair T middle middle k -> Prop}
    (hall : SixVertexMarkedDecoratedPairHall
      T lower middle upper k related) :
    (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val *
        sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <=
      (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
  rw [pow_two]
  rw [← sixVertexMarkedSectorPairMass_eq_coeff,
    ← sixVertexMarkedSectorPairMass_eq_coeff]
  exact sixVertexMarkedSectorPairMass_le_of_decoratedHall hall


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hall : forall k : Nat,
      exists related :
          SixVertexMarkedDecoratedPair T
              ⟨middle.val - 1, by omega⟩
              ⟨middle.val + 1, by omega⟩ k ->
            SixVertexMarkedDecoratedPair T middle middle k -> Prop,
        SixVertexMarkedDecoratedPairHall T
          ⟨middle.val - 1, by omega⟩ middle
          ⟨middle.val + 1, by omega⟩ k related) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  intro k
  obtain ⟨related, hhall⟩ := hall k
  have hcoeff := coeff_shiftedSectorTrace_mul_le_sq_of_decoratedHall hhall
  unfold sixVertexMarkedTraceLogConcavityDifference
  rw [Polynomial.coeff_sub]
  apply sub_nonneg.mpr
  simpa only [Fin.val_mk, pow_two] using hcoeff


theorem sixVertexSectorTrace_logConcave_of_decoratedHall
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hall : forall k : Nat,
      exists related :
          SixVertexMarkedDecoratedPair T
              ⟨middle.val - 1, by omega⟩
              ⟨middle.val + 1, by omega⟩ k ->
            SixVertexMarkedDecoratedPair T middle middle k -> Prop,
        SixVertexMarkedDecoratedPairHall T
          ⟨middle.val - 1, by omega⟩ middle
          ⟨middle.val + 1, by omega⟩ k related) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
  exact sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall
        T middle hmiddle_pos hmiddle_lt hall)

end
end StatMech.FrontierD

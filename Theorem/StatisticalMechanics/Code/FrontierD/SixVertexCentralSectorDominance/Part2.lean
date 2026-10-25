/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexWidthTopEigenvalue_eq_halfFilled_iff
    (N : Nat) (c : Real) :
    sixVertexWidthTopEigenvalue N c =
        sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c ↔
      ∀ m : Fin (N + 1),
        sixVertexWidthSectorTopEigenvalue N c m <=
          sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
  constructor
  · intro h m
    exact (sixVertexWidthSectorTopEigenvalue_le N c m).trans_eq h
  · intro h
    obtain ⟨m, hm⟩ := sixVertexWidthTopEigenvalue_exists_sector N c
    apply le_antisymm
    · rw [← hm]
      exact h m
    · let middle : Fin (N + 1) := ⟨N / 2, by omega⟩
      have hmiddle := sixVertexWidthSectorTopEigenvalue_le N c middle
      simpa [sixVertexWidthSectorTopEigenvalue, middle] using hmiddle


theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf
    (N : Nat) (hN : Even N) (c : Real)
    (hdom : ∀ n : Nat, (hn : n <= N / 2) ->
      sixVertexSectorTopEigenvalue N n (hn.trans (Nat.div_le_self N 2)) c <=
        sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  apply (sixVertexWidthTopEigenvalue_eq_halfFilled_iff N c).2
  intro m
  unfold sixVertexWidthSectorTopEigenvalue
  by_cases hm : m.val <= N / 2
  · exact hdom m.val hm
  · have hmN : m.val <= N := sixVertexWidthSectorIndex_le N m
    have hcomp : N - m.val <= N / 2 := by
      obtain ⟨k, hk⟩ := hN
      subst N
      omega
    have hparticle := sixVertexSectorTopEigenvalue_particleHole
      (N := N) (n := N - m.val) (Nat.sub_le N m.val) c
    have heq : sixVertexSectorTopEigenvalue N m.val hmN c =
        sixVertexSectorTopEigenvalue N (N - m.val)
          (Nat.sub_le N m.val) c := by
      simpa [Nat.sub_sub_self hmN] using hparticle
    rw [heq]
    exact hdom (N - m.val) hcomp


theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf
    (N : Nat) (hN : Even N) (hNpos : 0 < N)
    {c : Real} (hc : 0 < c)
    (hdom : SixVertexStrictLowerHalfDominance N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  have hhalf : 2 * (N / 2) = N := Nat.two_mul_div_two_of_even hN
  have hhalfPos : 0 < N / 2 := by omega
  have hcentralLower : 2 + c ^ N <=
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
    simpa using sixVertexHalfFilledSectorTop_ge_two_add_pow
      hhalfPos hhalf hc
  apply sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf N hN c
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    rw [sixVertexSectorTopEigenvalue_zero N hc]
    exact (le_add_of_nonneg_right (pow_nonneg hc.le N)).trans hcentralLower
  by_cases hnHalf : n = N / 2
  · subst n
    exact le_rfl
  · exact hdom n (Nat.pos_of_ne_zero hn0) (lt_of_le_of_ne hn hnHalf)


theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne
    (N : Nat) (hN : Even N) (hN4 : 4 <= N)
    {c : Real} (hc : 0 < c) (hc2 : 2 <= c)
    (hdom : SixVertexStrictLowerHalfDominanceAboveOne N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  apply sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf
    N hN (by omega) hc
  intro n hn0 hn
  by_cases hn1 : n = 1
  · subst n
    exact sixVertexSectorTopEigenvalue_one_le_halfFilled hN4
      (Nat.two_mul_div_two_of_even hN) hc hc2
  · exact hdom n (by omega) hn

end
end StatMech.FrontierD

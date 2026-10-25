/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleCut.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexFinPrefixIndex_val {N : Nat} (cut : Fin N)
    (i : Fin cut.val) : (sixVertexFinPrefixIndex cut i).val = i.val := rfl

@[simp] theorem sixVertexFinSuffixIndex_val {N : Nat} (cut : Fin N)
    (i : Fin (N - cut.val)) :
    (sixVertexFinSuffixIndex cut i).val = cut.val + i.val := rfl

theorem sixVertexFinPrefixIndex_injective {N : Nat} (cut : Fin N) :
    Function.Injective (sixVertexFinPrefixIndex cut) := by
  intro i j h
  apply Fin.ext
  have hval : (sixVertexFinPrefixIndex cut i).val =
      (sixVertexFinPrefixIndex cut j).val := congrArg Fin.val h
  exact hval

theorem sixVertexFinSuffixIndex_injective {N : Nat} (cut : Fin N) :
    Function.Injective (sixVertexFinSuffixIndex cut) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [sixVertexFinSuffixIndex_val] at hval
  omega

theorem sixVertexFinPrefixIndex_ne_suffixIndex {N : Nat} (cut : Fin N)
    (i : Fin cut.val) (j : Fin (N - cut.val)) :
    sixVertexFinPrefixIndex cut i ≠ sixVertexFinSuffixIndex cut j := by
  intro h
  have hval := congrArg Fin.val h
  simp only [sixVertexFinPrefixIndex_val, sixVertexFinSuffixIndex_val] at hval
  omega

theorem finitePeriodicSucc_prefixIndex
    {N : Nat} (hN : 0 < N) (cut : Fin N) (i : Nat)
    (hi : i + 1 < cut.val) :
    finitePeriodicSucc hN (sixVertexFinPrefixIndex cut ⟨i, by omega⟩) =
      sixVertexFinPrefixIndex cut ⟨i + 1, hi⟩ := by
  apply Fin.ext
  change (i + 1) % N = i + 1
  rw [Nat.mod_eq_of_lt]
  omega

theorem finitePeriodicSucc_suffixIndex
    {N : Nat} (hN : 0 < N) (cut : Fin N) (i : Nat)
    (hi : i + 1 < N - cut.val) :
    finitePeriodicSucc hN (sixVertexFinSuffixIndex cut ⟨i, by omega⟩) =
      sixVertexFinSuffixIndex cut ⟨i + 1, hi⟩ := by
  apply Fin.ext
  change (cut.val + i + 1) % N = cut.val + (i + 1)
  rw [Nat.mod_eq_of_lt]
  · omega
  · have := cut.isLt
    omega


end
end StatMech.FrontierD

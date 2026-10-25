/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionSurfaceAssembly
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedConnectedInsertionCarrier
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem cyclicPred_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (SixVertexArrows.cyclicPred hN) := by
  intro x y h
  rw [← finitePeriodicSucc_cyclicPred hN x,
    ← finitePeriodicSucc_cyclicPred hN y, h]

theorem even_cyclicPred_iff_not {N : Nat} (hN : 0 < N)
    (hEven : Even N) (i : Fin N) :
    Even (SixVertexArrows.cyclicPred hN i).val ↔ ¬ Even i.val := by
  let z := SixVertexArrows.cyclicPred hN i
  have hsucc : Even (finitePeriodicSucc hN z).val ↔ ¬ Even z.val := by
    change Even ((z.val + 1) % N) ↔ ¬ Even z.val
    rw [Even.mod_even_iff hEven, Nat.even_add_one]
  rw [finitePeriodicSucc_cyclicPred] at hsucc
  tauto

theorem cyclicPred_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (SixVertexArrows.cyclicPred hN i).val =
      if i.val = 0 then N - 1 else i.val - 1 := by
  unfold SixVertexArrows.cyclicPred
  simp only [Fin.val_mk]
  by_cases hi : i.val = 0
  · rw [if_pos hi, hi, zero_add,
      Nat.mod_eq_of_lt (Nat.sub_lt hN Nat.zero_lt_one)]
  · rw [if_neg hi]
    have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
    have heq : i.val + N - 1 = (i.val - 1) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega

theorem cyclicPred_cyclicPred_ne_self {N : Nat}
    (hN : 2 < N) (i : Fin N) :
    SixVertexArrows.cyclicPred (by omega)
        (SixVertexArrows.cyclicPred (by omega) i) ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  let p := SixVertexArrows.cyclicPred (by omega : 0 < N) i
  have hp := cyclicPred_val (N := N) (by omega) i
  have hpp := cyclicPred_val (N := N) (by omega) p
  by_cases hi0 : i.val = 0
  · rw [if_pos hi0] at hp
    have hp0 : p.val ≠ 0 := by dsimp [p] at hp ⊢; omega
    rw [if_neg hp0] at hpp
    dsimp [p] at hpp hval
    omega
  · rw [if_neg hi0] at hp
    by_cases hi1 : i.val = 1
    · have hp0 : p.val = 0 := by dsimp [p] at hp ⊢; omega
      rw [if_pos hp0] at hpp
      dsimp [p] at hpp hval
      omega
    · have hp0 : p.val ≠ 0 := by dsimp [p] at hp ⊢; omega
      rw [if_neg hp0] at hpp
      dsimp [p] at hpp hval
      omega

set_option maxHeartbeats 1000000 in
theorem fkRectTorusIndexedEdge_injective (R : FKRectTorus) :
    Function.Injective (fkRectTorusIndexedEdge R) := by
  rintro ⟨b, x, y⟩ ⟨c, u, v⟩ h
  cases b <;> cases c <;>
    by_cases hy : Even y.val <;> by_cases hv : Even v.val <;>
    simp [fkRectTorusIndexedEdge, hy, hv, Sym2.eq_iff] at h ⊢
  all_goals
    have hxne := cyclicPred_ne_self
      (lt_trans Nat.one_lt_two R.width_gt_two)
    have hyne := cyclicPred_ne_self
      (lt_trans Nat.one_lt_two R.height_gt_two)
    have hypred := even_cyclicPred_iff_not R.height_pos R.height_even
    have hxinj := cyclicPred_injective R.width_pos
    have hyinj := cyclicPred_injective R.height_pos
    have hxtwo := cyclicPred_cyclicPred_ne_self R.width_gt_two
    have hytwo := cyclicPred_cyclicPred_ne_self R.height_gt_two
    rcases h with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    all_goals aesop (config := { maxRuleApplications := 50 })
    all_goals exact hxne _ h3.symm


end
end StatMech.FrontierD

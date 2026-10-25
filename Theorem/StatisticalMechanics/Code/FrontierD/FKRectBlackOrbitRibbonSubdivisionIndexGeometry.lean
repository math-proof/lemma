/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonSubdivisionIndexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionCodeInjective
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonSubdivisionIndexGeometry


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem finSigmaFinEquiv_fkRectFinSigmaSucc {n : ℕ}
    (scale : Fin n → ℕ) (hscale : ∀ i, 0 < scale i)
    [NeZero (∑ i, scale i)] (z : Σ i, Fin (scale i)) :
    finSigmaFinEquiv (fkRectFinSigmaSucc scale hscale z) =
      finSigmaFinEquiv z + 1 := by
  rcases z with ⟨i, r⟩
  have hn : n ≠ 0 := fun hn => Fin.elim0 (hn ▸ i)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [fkRectFinSigmaSucc]
  split_ifs with hr
  · apply Fin.ext
    rw [finSigmaFinEquiv_apply]
    have hlt : (finSigmaFinEquiv ⟨i, r⟩).val + 1 <
        ∑ j, scale j := by
      simpa [finSigmaFinEquiv_apply] using
        (finSigmaFinEquiv
          (⟨i, ⟨r.val + 1, hr⟩⟩ : Σ i, Fin (scale i))).isLt
    rw [Fin.val_add_one_of_lt' hlt, finSigmaFinEquiv_apply]
    rfl
  · have hrval : r.val + 1 = scale i := by omega
    by_cases hi : i = Fin.last m
    · subst i
      let zzero : Σ i, Fin (scale i) :=
        ⟨0, ⟨0, hscale 0⟩⟩
      have htarget :
          (⟨Fin.last m + 1, ⟨0, hscale (Fin.last m + 1)⟩⟩ :
            Σ i, Fin (scale i)) = zzero := by
        rw [Fin.last_add_one]
      rw [htarget]
      let N := ∑ i, scale i
      have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      let lastN : Fin N := ⟨N - 1, by omega⟩
      have hzero : finSigmaFinEquiv zzero = 0 := by
        apply Fin.ext
        simp [zzero, finSigmaFinEquiv_apply]
      have hlast : finSigmaFinEquiv
          (⟨Fin.last m, r⟩ : Σ i, Fin (scale i)) = lastN := by
        apply Fin.ext
        rw [finSigmaFinEquiv_apply]
        dsimp [lastN, N]
        have hprefixLast :
            (∑ i : Fin m,
              scale (Fin.castLE (LT.lt.le (Fin.last m).isLt) i)) =
              ∑ i : Fin m, scale i.castSucc := by
          apply Finset.sum_congr rfl
          intro x hx
          congr 1
        change
          (∑ i : Fin m,
              scale (Fin.castLE (LT.lt.le (Fin.last m).isLt) i)) + r.val =
            (∑ i, scale i) - 1
        rw [hprefixLast, Fin.sum_univ_castSucc scale]
        omega
      rw [hzero, hlast]
      change (0 : Fin N) = lastN + 1
      by_cases hN1 : N = 1
      · apply Fin.ext
        simp [lastN, hN1, Fin.add_def]
      · have h1N : 1 < N := by omega
        have hone : ((1 : Fin N) : ℕ) = 1 := by
          change 1 % N = 1
          exact Nat.mod_eq_of_lt h1N
        apply Fin.ext
        simp only [Fin.val_zero, Fin.val_add, hone]
        dsimp only [lastN]
        rw [show N - 1 + 1 = N by omega, Nat.mod_self]
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      have hnext : j.castSucc + 1 = j.succ := by
        apply Fin.ext
        exact Fin.val_add_one_of_lt (by simp)
      let znext : Σ i, Fin (scale i) :=
        ⟨j.succ, ⟨0, hscale j.succ⟩⟩
      have htarget :
          (⟨j.castSucc + 1, ⟨0, hscale (j.castSucc + 1)⟩⟩ :
            Σ i, Fin (scale i)) = znext := by
        rw [hnext]
      rw [htarget]
      have hprefix :
          (∑ x : Fin (j.val + 1),
              scale (Fin.castLE (LT.lt.le j.succ.isLt) x)) =
            (∑ x : Fin j.val,
              scale (Fin.castLE (LT.lt.le j.castSucc.isLt) x)) +
              scale j.castSucc := by
        rw [Fin.sum_univ_castSucc]
        congr 1
      have hval :
          (finSigmaFinEquiv
            (⟨j.castSucc, r⟩ : Σ i, Fin (scale i))).val + 1 =
            (finSigmaFinEquiv znext).val := by
        dsimp [znext]
        rw [finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
        simp only [Fin.val_succ, Fin.val_castSucc]
        change
          (∑ x : Fin j.val,
              scale (Fin.castLE (LT.lt.le j.castSucc.isLt) x)) +
                r.val + 1 =
            (∑ x : Fin (j.val + 1),
              scale (Fin.castLE (LT.lt.le j.succ.isLt) x)) + 0
        rw [hprefix]
        omega
      have hlt : (finSigmaFinEquiv
          (⟨j.castSucc, r⟩ : Σ i, Fin (scale i))).val + 1 <
          ∑ i, scale i := by
        rw [hval]
        exact (finSigmaFinEquiv znext).isLt
      apply Fin.ext
      rw [Fin.val_add_one_of_lt' hlt]
      exact hval.symm

set_option maxHeartbeats 500000 in

theorem fkRectBlackOrbitRibbonSubdivisionWord_length_eq_sum
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    (fkRectBlackOrbitRibbonSubdivisionWord R omega d).length =
      ∑ k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length,
        onsAnisotropicStepScale (8 * R.medialTorus.width)
          (8 * R.medialTorus.height)
          (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) := by
  have hw : 16 * R.width = 8 * (2 * R.width) := by ring
  simp_rw [fkRectBlackOrbitMedialRibbonFlatDirection_eq_get]
  unfold fkRectBlackOrbitRibbonSubdivisionWord
  rw [show 16 * R.width = 8 * R.medialTorus.width by
      simpa [FKRectTorus.medialTorus] using hw]
  unfold onsAnisotropicDirectionWord
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  rw [← List.sum_ofFn]
  rw [← List.ofFn_get (fkRectBlackOrbitMedialRibbonWord R omega d),
    List.map_ofFn]
  simp only [List.ofFn_get, Function.comp_apply]
  simp [FKRectTorus.medialTorus]


end
end StatMech.FrontierD

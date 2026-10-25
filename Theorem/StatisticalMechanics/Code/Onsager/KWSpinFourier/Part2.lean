/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part2


namespace StatMech.Onsager

theorem ons_KWmatPhase_translation_invariant (L : ℕ) (x omega u v : ℂ)
    (t : ZMod L × ZMod L) (d1 d2 : ons_Dart L) :
    ons_KWmatPhase L x omega u v (ons_shiftDart L t d2) (ons_shiftDart L t d1) =
      ons_KWmatPhase L x omega u v d2 d1 := by
  unfold ons_KWmatPhase
  rw [ons_KWmat_translation_invariant]
  rfl

theorem ons_KWmatPhase_eq_blockCirc (L : ℕ) (x omega u v : ℂ) :
    ons_KWmatPhase L x omega u v =
      ons_blockCirculant2D L 4 (ons_KWblockPhase L x omega u v) := by
  ext p q
  show ons_KWmatPhase L x omega u v p q =
    ons_KWmatPhase L x omega u v
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) ((0 : ZMod L × ZMod L), q.2)
  have h := ons_KWmatPhase_translation_invariant L x omega u v q.1
    ((0 : ZMod L × ZMod L), q.2)
    ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2)
  simpa [ons_shiftDart] using h

theorem ons_KWblockPhaseSymbol_eq (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x omega u v root : ℂ) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 4 root
      (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
        ons_KWblockPhase L x omega u v g) j =
      ons_KWsymbolMat x omega (u * root ^ j.1.val) (v * root ^ j.2.val) := by
  have hLne : L ≠ 0 := NeZero.ne L
  have hrootne : root ≠ 0 := hroot.ne_zero hLne
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hLne
    rw [ZMod.val_neg_one]
  have hbase : root ^ ((-1 : ZMod L).val) = root⁻¹ := by
    have h1 : root ^ ((-1 : ZMod L).val) * root = 1 := by
      rw [← pow_succ, hval, hroot.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left h1).symm
  have hinv : ∀ m : ℕ, root ^ ((-1 : ZMod L).val * m) = (root ^ m)⁻¹ := by
    intro m
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hid : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        (if k = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) a b) =
      (if a = b then 1 else 0 : ℂ) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp [Matrix.one_apply]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hkw : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        ons_KWblockPhase L x omega u v k a b) =
      root ^ ((ons_dirStep L b 0).1.val * j.1.val +
        (ons_dirStep L b 0).2.val * j.2.val) *
        (ons_dirPhase u v b * (x * ons_turnW omega b a)) := by
    have hentry : ∀ k : ZMod L × ZMod L,
        ons_KWblockPhase L x omega u v k a b =
          if k = ons_dirStep L b 0 then
            ons_dirPhase u v b * (x * ons_turnW omega b a) else 0 := by
      intro k
      unfold ons_KWblockPhase ons_KWmatPhase ons_KWmat
      simp only [Prod.fst, Prod.snd]
      by_cases hk : k = ons_dirStep L b 0 <;> simp [hk] <;> ring
    simp only [hentry]
    rw [Finset.sum_eq_single (ons_dirStep L b 0)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  have homegane : omega ≠ 0 := by
    intro h
    rw [h] at homega
    simp at homega
    exact Complex.I_ne_zero homega.symm
  have hturn : omega⁻¹ = -Complex.I * omega := by
    have key : (-Complex.I * omega) * omega = 1 := by
      calc
        (-Complex.I * omega) * omega = -Complex.I * omega ^ 2 := by ring
        _ = 1 := by rw [homega, neg_mul, Complex.I_mul_I, neg_neg]
    exact inv_eq_of_mul_eq_one_left key
  fin_cases b <;>
    simp only [ons_dirStep, ons_dirPhase] <;>
    fin_cases a <;>
    simp only [ons_KWsymbolMat, ons_turnW, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val'] <;>
    simp_all [hinv, hturn, ZMod.val_one, one_mul, mul_one, mul_inv_rev] <;>
    field_simp <;> ring


theorem ons_KWmatPhase_det_eq_prod (L : ℕ) [NeZero L] [Fact (1 < L)]
    (x omega u v root : ℂ) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 - ons_KWmatPhase L x omega u v).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) ^ 2 - x * (1 - x ^ 2) *
          (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹ +
            (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹))) := by
  have hblock : (1 - ons_KWmatPhase L x omega u v) =
      ons_blockCirculant2D L 4
        (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
          ons_KWblockPhase L x omega u v g) := by
    rw [ons_KWmatPhase_eq_blockCirc]
    ext p q
    simp only [Matrix.sub_apply]
    show (1 : Matrix (ons_Dart L) (ons_Dart L) ℂ) p q -
        ons_blockCirculant2D L 4 (ons_KWblockPhase L x omega u v) p q =
      ons_blockCirculant2D L 4
        (fun g => (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) ℂ) else 0) -
          ons_KWblockPhase L x omega u v g) p q
    unfold ons_blockCirculant2D
    simp only [Matrix.sub_apply]
    congr 1
    rw [Matrix.one_apply]
    by_cases hpq : p = q
    · subst p
      simp [Matrix.one_apply]
    · rw [if_neg hpq]
      by_cases hg : (p.1.1 - q.1.1, p.1.2 - q.1.2) = 0
      · rw [if_pos hg, Matrix.one_apply]
        have hdir : p.2 ≠ q.2 := by
          intro hdir
          apply hpq
          apply Prod.ext
          · apply Prod.ext <;> dsimp only at hg ⊢
            · exact sub_eq_zero.mp (congrArg Prod.fst hg)
            · exact sub_eq_zero.mp (congrArg Prod.snd hg)
          · exact hdir
        rw [if_neg hdir]
      · rw [if_neg hg]
        simp
  rw [hblock, ons_det_blockCirculant2D L 4 root hroot]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_KWblockPhaseSymbol_eq L x omega u v root homega hroot hu hv j]
  rw [ons_symbol_det_z x omega _ _ homega
    (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))]
  ring


end StatMech.Onsager

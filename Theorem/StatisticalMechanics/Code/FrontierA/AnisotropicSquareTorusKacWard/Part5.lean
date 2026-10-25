/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem anisotropicSquareKWMatrixPhase_translation_invariant
    (L : Nat) (x y omega u v : Complex)
    (t : ZMod L × ZMod L) (d₁ d₂ : ons_Dart L) :
    anisotropicSquareKWMatrixPhase L x y omega u v
        (ons_shiftDart L t d₂) (ons_shiftDart L t d₁) =
      anisotropicSquareKWMatrixPhase L x y omega u v d₂ d₁ := by
  unfold anisotropicSquareKWMatrixPhase ons_shiftDart
  simp only
  have hstep := ons_dirStep_shift L d₁.2 t d₁.1
  rw [hstep]
  have hiff :
      ((d₂.1.1 + t.1, d₂.1.2 + t.2) =
          ((ons_dirStep L d₁.2 d₁.1).1 + t.1,
            (ons_dirStep L d₁.2 d₁.1).2 + t.2)) ↔
        d₂.1 = ons_dirStep L d₁.2 d₁.1 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨add_right_cancel h₁, add_right_cancel h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by rw [h₁], by rw [h₂]⟩
  by_cases hconnect : d₂.1 = ons_dirStep L d₁.2 d₁.1
  · rw [if_pos (hiff.mpr hconnect), if_pos hconnect]
  · rw [if_neg (fun h ↦ hconnect (hiff.mp h)), if_neg hconnect]

theorem anisotropicSquareKWMatrixPhase_eq_blockCirculant
    (L : Nat) (x y omega u v : Complex) :
    anisotropicSquareKWMatrixPhase L x y omega u v =
      ons_blockCirculant2D L 4
        (anisotropicSquareKWBlockPhase L x y omega u v) := by
  ext p q
  show anisotropicSquareKWMatrixPhase L x y omega u v p q =
    anisotropicSquareKWMatrixPhase L x y omega u v
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2) (0, q.2)
  have h := anisotropicSquareKWMatrixPhase_translation_invariant
    L x y omega u v q.1 (0, q.2)
      ((p.1.1 - q.1.1, p.1.2 - q.1.2), p.2)
  simpa [ons_shiftDart] using h

theorem anisotropicSquareKWBlockPhase_symbol
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y omega u v root : Complex) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0)
    (j : ZMod L × ZMod L) :
    ons_blockSymbol2D L 4 root
      (fun g ↦ (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) -
        anisotropicSquareKWBlockPhase L x y omega u v g) j =
      anisotropicSquareKWSymbolMatrix x y omega
        (u * root ^ j.1.val) (v * root ^ j.2.val) := by
  have hrootne : root ≠ 0 := hroot.ne_zero (NeZero.ne L)
  have hval : (-1 : ZMod L).val + 1 = L := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    rw [ZMod.val_neg_one]
  have hbase : root ^ ((-1 : ZMod L).val) = root⁻¹ := by
    have hmul : root ^ ((-1 : ZMod L).val) * root = 1 := by
      rw [← pow_succ, hval, hroot.pow_eq_one]
    exact (inv_eq_of_mul_eq_one_left hmul).symm
  have hinv (m : Nat) : root ^ ((-1 : ZMod L).val * m) = (root ^ m)⁻¹ := by
    rw [pow_mul, hbase, inv_pow]
  ext a b
  simp only [ons_blockSymbol2D, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hid : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        (if k = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) a b) =
      (if a = b then 1 else 0 : Complex) := by
    rw [Finset.sum_eq_single (0 : ZMod L × ZMod L)]
    · simp [Matrix.one_apply]
    · intro k _ hk
      rw [if_neg hk]
      simp
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  have hkw : (∑ k : ZMod L × ZMod L,
      root ^ (k.1.val * j.1.val + k.2.val * j.2.val) *
        anisotropicSquareKWBlockPhase L x y omega u v k a b) =
      root ^ ((ons_dirStep L b 0).1.val * j.1.val +
        (ons_dirStep L b 0).2.val * j.2.val) *
        (ons_dirPhase u v b *
          (squareTorusDirectionWeight x y b * ons_turnW omega b a)) := by
    have hentry (k : ZMod L × ZMod L) :
        anisotropicSquareKWBlockPhase L x y omega u v k a b =
          if k = ons_dirStep L b 0 then
            ons_dirPhase u v b *
              (squareTorusDirectionWeight x y b * ons_turnW omega b a)
          else 0 := by
      unfold anisotropicSquareKWBlockPhase anisotropicSquareKWMatrixPhase
      simp only [Prod.fst, Prod.snd]
      by_cases hk : k = ons_dirStep L b 0 <;> simp [hk]
    simp only [hentry]
    rw [Finset.sum_eq_single (ons_dirStep L b 0)]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · exact fun h ↦ absurd (Finset.mem_univ _) h
  rw [hid, hkw]
  have homegane : omega ≠ 0 := by
    intro h
    rw [h] at homega
    simp at homega
    exact Complex.I_ne_zero homega.symm
  have hturn : omega⁻¹ = -Complex.I * omega := by
    apply inv_eq_of_mul_eq_one_left
    calc
      (-Complex.I * omega) * omega = -Complex.I * omega ^ 2 := by ring
      _ = 1 := by rw [homega, neg_mul, Complex.I_mul_I, neg_neg]
  fin_cases b <;>
    simp only [ons_dirStep, ons_dirPhase, squareTorusDirectionWeight] <;>
    fin_cases a <;>
    simp only [anisotropicSquareKWSymbolMatrix, ons_turnW,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val'] <;>
    simp_all [hinv, hturn, ZMod.val_one, one_mul, mul_one, mul_inv_rev] <;>
    field_simp <;> ring


theorem anisotropicSquareKWMatrixPhase_det
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y omega u v root : Complex) (homega : omega ^ 2 = Complex.I)
    (hroot : IsPrimitiveRoot root L) (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 - anisotropicSquareKWMatrixPhase L x y omega u v).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          x * (1 - y ^ 2) *
            (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹) -
          y * (1 - x ^ 2) *
            (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹)) := by
  have hblock : (1 - anisotropicSquareKWMatrixPhase L x y omega u v) =
      ons_blockCirculant2D L 4
        (fun g ↦ (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) -
          anisotropicSquareKWBlockPhase L x y omega u v g) := by
    rw [anisotropicSquareKWMatrixPhase_eq_blockCirculant]
    ext p q
    simp only [Matrix.sub_apply]
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
  rw [anisotropicSquareKWBlockPhase_symbol L x y omega u v root
    homega hroot hu hv j]
  exact anisotropicSquareKWSymbolMatrix_det x y omega _ _ homega
    (mul_ne_zero hu (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))
    (mul_ne_zero hv (pow_ne_zero _ (hroot.ne_zero (NeZero.ne L))))


theorem anisotropicSquareKWMatrixPhase_det_eq_cosProduct
    (L : Nat) [NeZero L] [Fact (1 < L)]
    (x y : Complex) (a b : Fin 2) :
    (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      ∏ j : ZMod L × ZMod L,
        ((1 + x ^ 2) * (1 + y ^ 2) -
          2 * x * (1 - y ^ 2) *
            Real.cos (2 * Real.pi *
              (j.1.val + (a.val : Real) / 2) / L) -
          2 * y * (1 - x ^ 2) *
            Real.cos (2 * Real.pi *
              (j.2.val + (b.val : Real) / 2) / L)) := by
  rw [anisotropicSquareKWMatrixPhase_det L x y ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
  push_cast
  ring


end StatMech.FrontierA

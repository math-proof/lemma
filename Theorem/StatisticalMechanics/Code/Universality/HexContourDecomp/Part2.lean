/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part4
import Structure.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


namespace HexBoundaryDecomp

variable {V : Type*} [DecidableEq V] {D : HexDomain V} {P : D.InteriorPairing}
  (B : HexBoundaryDecomp D P)


theorem boundarySum_eq_sum_sides :
    D.boundarySum P
      = B.A.incSum + B.L.incSum + B.Tp.incSum + B.Tm.incSum + B.U.incSum := by
  unfold HexDomain.boundarySum HexSide.incSum
  rw [B.partition]
  
  rw [Finset.sum_union (by
        
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left,
            Finset.disjoint_union_left]
        exact ⟨⟨⟨B.disjAU, B.disjLU⟩, B.disjTpU⟩, B.disjTmU⟩)]
  rw [Finset.sum_union (by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨B.disjATm, B.disjLTm⟩, B.disjTpTm⟩)]
  rw [Finset.sum_union (by
        rw [Finset.disjoint_union_left]
        exact ⟨B.disjATp, B.disjLTp⟩)]
  rw [Finset.sum_union B.disjAL]


theorem boundarySum_eq :
    D.boundarySum P
      = Complex.I * (((hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups : ℝ)
          - (B.Fa : ℝ)) : ℂ) := by
  rw [B.boundarySum_eq_sum_sides]
  rw [B.A.incSum_eq_dir_mul_fSum, B.L.incSum_eq_dir_mul_fSum,
      B.Tp.incSum_eq_dir_mul_fSum, B.Tm.incSum_eq_dir_mul_fSum,
      B.U.incSum_eq_dir_mul_fSum]
  rw [B.projA, B.projL, B.projTp, B.projTm, B.projU]
  push_cast
  ring

end HexBoundaryDecomp


theorem hexBoundary_identity_via_decomp {V : Type*} [DecidableEq V]
    (D : HexDomain V) (P : D.InteriorPairing) (hsub : P.interior ⊆ D.incidences)
    (B : HexBoundaryDecomp D P) (hFa : B.Fa = 1) :
    hexBdryCl * B.lam + hexBdryCt * (B.taup + B.taum) + B.ups = 1 := by
  refine hexBoundary_of_decomp B.lam (B.taup + B.taum) B.ups B.Fa
    (D.boundarySum P) ?_ hFa B.boundarySum_eq
  exact D.hexBoundaryRaw P hsub


theorem hexBoundary_identity_scales_via_decomp {V : Type*} [DecidableEq V]
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (hsub : ∀ v, (P v).interior ⊆ (D v).incidences)
    (B : ∀ v, HexBoundaryDecomp (D v) (P v))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (B v).lam + hexBdryCt * ((B v).taup + (B v).taum) + (B v).ups = 1 := by
  intro v hv
  exact hexBoundary_identity_via_decomp (D v) (P v) (hsub v) (B v) (hFa v hv)


theorem hexDecomp_hdecomp {V : Type*} [DecidableEq V]
    (D : ℕ → HexDomain V) (P : ∀ v, (D v).InteriorPairing)
    (B : ∀ v, HexBoundaryDecomp (D v) (P v)) :
    ∀ v, 1 ≤ v → (D v).boundarySum (P v)
      = Complex.I * ((hexBdryCl * (B v).lam
          + hexBdryCt * ((B v).taup + (B v).taum) + (B v).ups : ℝ) - ((B v).Fa : ℝ)) := by
  intro v _
  exact (B v).boundarySum_eq


theorem hexDecomp_projL_realize (c : ℂ) :
    (Complex.I * Complex.exp ((-(3 * Real.pi / 8) : ℝ) * Complex.I))
        * (Complex.exp ((3 * Real.pi / 8 : ℝ) * Complex.I) * ((hexBdryCl : ℂ) * c))
      = Complex.I * ((hexBdryCl : ℂ) * c) := by
  have h := HexSide.proj_of_tilt (3 * Real.pi / 8) c
  rwa [show (Real.cos (3 * Real.pi / 8) : ℂ) = (hexBdryCl : ℂ) from rfl] at h


theorem hexDecomp_projT_realize (c : ℂ) :
    (Complex.I * Complex.exp ((-(Real.pi / 4) : ℝ) * Complex.I))
        * (Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) * ((hexBdryCt : ℂ) * c))
      = Complex.I * ((hexBdryCt : ℂ) * c) := by
  have h := HexSide.proj_of_tilt (Real.pi / 4) c
  rwa [show (Real.cos (Real.pi / 4) : ℂ) = (hexBdryCt : ℂ) from rfl] at h


theorem hexDecomp_projU_realize (c : ℂ) :
    (Complex.I * Complex.exp ((-(0 : ℝ)) * Complex.I))
        * (Complex.exp ((0 : ℝ) * Complex.I) * ((1 : ℂ) * c))
      = Complex.I * c := by
  have h := HexSide.proj_of_tilt 0 c
  simp only [Real.cos_zero, Complex.ofReal_one, one_mul, neg_zero] at h
  simpa only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using h

end StatMech.Universality

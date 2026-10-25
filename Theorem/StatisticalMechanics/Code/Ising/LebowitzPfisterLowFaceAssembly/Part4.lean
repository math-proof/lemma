/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part4
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma radialTerm_bernstein_sum (t : TriTerm) (r q h : Real)
    (hex : t.ex <= 6) (hey : t.ey <= 6) (hez : t.ez <= 3) :
    (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
      (radialTermCoeff t a b c : Real) *
        bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) =
      (27720 * 105 * 3 : Real) * t.eval r q h := by
  have ha := scaledBernFactor_sum_twelve t.ex hex r
  have hb := scaledBernFactor_sum_seven t.ey hey q
  have hc := scaledBernFactor_sum_three t.ez hez h
  simp only [radialTermCoeff]
  push_cast
  calc
    (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
      (t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
        scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c *
        bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) =
      ∑ a : Fin 13, ∑ b : Fin 8,
        ((t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
          bernsteinWeight 12 a r * scaledBernFactor 7 105 t.ey b *
          bernsteinWeight 7 b q) * (3 * h ^ t.ez) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [← hc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ = ∑ a : Fin 13,
        ((t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
          bernsteinWeight 12 a r) * (105 * q ^ t.ey) * (3 * h ^ t.ez) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← hb, Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = (t.coeff : Real) * (27720 * r ^ t.ex) *
        (105 * q ^ t.ey) * (3 * h ^ t.ez) := by
        rw [← ha, Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = (27720 * 105 * 3 : Real) * t.eval r q h := by
        simp only [TriTerm.eval]
        push_cast
        ring

lemma bernsteinEvalTerms_eq (ts : List TriTerm) (r q h : Real)
    (hbounds : ∀ t ∈ ts, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3) :
    bernsteinEvalTerms ts r q h =
      (27720 * 105 * 3 : Real) * evalTerms ts r q h := by
  induction ts with
  | nil => simp [bernsteinEvalTerms, radialCoeffTerms, evalTerms]
  | cons t ts ih =>
      have ht := hbounds t (by simp)
      have hts : ∀ s ∈ ts, s.ex <= 6 ∧ s.ey <= 6 ∧ s.ez <= 3 := by
        intro s hs
        exact hbounds s (by simp [hs])
      rw [show bernsteinEvalTerms (t :: ts) r q h =
        (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
          (radialTermCoeff t a b c : Real) *
            bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) +
          bernsteinEvalTerms ts r q h by
        simp only [bernsteinEvalTerms, radialCoeffTerms]
        push_cast
        simp_rw [add_mul, Finset.sum_add_distrib],
        radialTerm_bernstein_sum t r q h ht.1 ht.2.1 ht.2.2,
        ih hts]
      rw [evalTerms]
      ring

lemma TriPoly.eval_nonneg_of_bernstein
    (p : TriPoly) (r q h : Real)
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hq0 : 0 <= q) (hq1 : q <= 1)
    (hh0 : 0 <= h) (hh1 : h <= 1)
    (hbounds : ∀ t ∈ p.terms, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3)
    (hcoeff : ∀ (a : Fin 13) (b : Fin 8) (c : Fin 4),
      0 <= radialBernCoeffOf p a b c) :
    0 <= p.eval r q h := by
  have hsum : 0 <= bernsteinEvalTerms p.terms r q h := by
    unfold bernsteinEvalTerms
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    rw [← radialBernCoeffOf_eq]
    have hcR : (0 : Real) <= radialBernCoeffOf p a b c := by
      exact_mod_cast hcoeff a b c
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcR
          (bernsteinWeight_nonneg hr0 hr1))
        (bernsteinWeight_nonneg hq0 hq1))
      (bernsteinWeight_nonneg hh0 hh1)
  rw [bernsteinEvalTerms_eq p.terms r q h hbounds] at hsum
  norm_num at hsum ⊢
  simpa [TriPoly.eval] using hsum

theorem radializedCrossCoeff_eval_nonneg
    (i j k : Fin 8) (r q h : Real)
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hq0 : 0 <= q) (hq1 : q <= 1)
    (hh0 : 0 <= h) (hh1 : h <= 1) :
    0 <= (radialize (crossCoeffPoly i j k)).eval r q h := by
  apply TriPoly.eval_nonneg_of_bernstein _ r q h
    hr0 hr1 hq0 hq1 hh0 hh1
  · exact radializedCrossCoeff_bounds i j k
  · intro a b c
    exact radialBernCoeff_nonneg i j k a b c

end LowFaceCertificate
end
end StatMech.Ising

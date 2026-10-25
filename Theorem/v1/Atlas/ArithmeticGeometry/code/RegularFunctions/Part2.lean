/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites
import Def.v1.Atlas.ArithmeticGeometry.code.RegularFunctions.Part3
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- Key technical lemma: the substitution homomorphism associated to a rational map
$\varphi : X \dashrightarrow Y$ kills the ideal $\mathcal{I}(Y)$. Combines the
Nullstellensatz with the property that the values of $\varphi$ land in $Y$. This is what
allows the substitution map to descend to $\bar k[Y] \to \bar k(X)$. -/
theorem dominantPullbackSubstHom_kills_ideal
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    dominantPullbackSubstHom φ.components f = 0 := by


  by_contra hr

  obtain ⟨⟨a_r, ⟨b_r, hb_r⟩⟩, hab_r⟩ := IsLocalization.surj
    (nonZeroDivisors (AffineCoordinateRingBar X))
    (dominantPullbackSubstHom φ.components f)
  simp only at hab_r

  have ha_ne : a_r ≠ 0 := by
    intro ha0; apply hr
    have h1 : dominantPullbackSubstHom φ.components f *
        (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r = 0 := by
      rw [hab_r, ha0, map_zero]
    have hb_ne_frac : (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.mp hb_r
    exact (mul_eq_zero.mp h1).resolve_right hb_ne_frac
  have hb_ne : b_r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_r

  choose cd_j hcd_j using
    (fun j => IsLocalization.surj (nonZeroDivisors (AffineCoordinateRingBar X)) (φ.components j))

  set product := a_r * (b_r * ∏ j : Fin n_cod, ((cd_j j).2 : AffineCoordinateRingBar X))
    with hprod_def

  have hprod_ne : product ≠ 0 := by
    apply mul_ne_zero ha_ne (mul_ne_zero hb_ne _)
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (cd_j j).2.property)


  have h_clearing : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg_comp : IsTupleRegularAt φ.components P hP)
      (p : MvPolynomial (Fin n_cod) (AlgebraicClosure k)),
      ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
        evalBarAtPoint k X P hP g₀ ≠ 0 ∧
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) f₀ =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) g₀ *
          (dominantPullbackSubstHom φ.components) p ∧
        MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) p *
          evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
    intro P hP hreg_comp p
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
      · simp [map_one]
      · simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          map_one, one_mul]
        rfl
      · simp only [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
    | add p q ihp ihq =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
      refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
      · simp only [map_mul, map_add]
        rw [mul_add]
        congr 1
        · rw [hfp_eq]; ring
        · rw [hfq_eq]; ring
      · simp only [map_mul, map_add]
        linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
          (evalBarAtPoint k X P hP gp) * hfq_eval
    | mul_X p j ihp =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg_comp j
      obtain ⟨aj, haj_eq⟩ := hgj_mem
      refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
      · simp only [map_mul]
        rw [show (dominantPullbackSubstHom φ.components) (MvPolynomial.X j) =
          φ.components j by
          simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X']]
        rw [hfp_eq, haj_eq]
        ring
      · simp only [MvPolynomial.eval_X, map_mul]
        have hσj : evalTupleAt φ.components P hP hreg_comp j *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
          set g₀ := (hreg_comp j).choose with hg₀_def
          set f₀ := (hreg_comp j).choose_spec.2.choose with hf₀_def
          have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := (hreg_comp j).choose_spec.1
          have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) f₀ =
            (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) g₀ * φ.components j :=
            (hreg_comp j).choose_spec.2.choose_spec
          have h_cross : f₀ * gj = aj * g₀ := by
            apply IsFractionRing.injective (AffineCoordinateRingBar X)
              (FractionRing (AffineCoordinateRingBar X))
            simp only [map_mul]
            rw [hf₀_eq, haj_eq]
            ring
          show evalRatFunAt (φ.components j) P hP (hreg_comp j) *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj
          simp only [evalRatFunAt]
          rw [div_mul_eq_mul_div, div_eq_iff hg₀_ne]
          rw [← map_mul, ← map_mul, h_cross]
        calc (MvPolynomial.eval _ p) *
              (evalTupleAt φ.components P hP hreg_comp j) *
              ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
            = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
              ((evalTupleAt φ.components P hP hreg_comp j) *
               (evalBarAtPoint k X P hP gj)) := by ring
          _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
              rw [hfp_eval, hσj]

  have hprod_vanishes : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X),
      evalBarAtPoint k X P hP product = 0 := by
    intro P hP
    simp only [hprod_def, map_mul, map_prod]
    by_cases hbP : evalBarAtPoint k X P hP b_r = 0
    · simp [hbP]
    by_cases hdP : ∃ j, evalBarAtPoint k X P hP ((cd_j j).2 : AffineCoordinateRingBar X) = 0
    · obtain ⟨j, hjP⟩ := hdP
      have : (∏ i : Fin n_cod,
          evalBarAtPoint k X P hP ((cd_j i).2 : AffineCoordinateRingBar X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hjP
      simp [this]
    push Not at hdP

    have hreg_comp : IsTupleRegularAt φ.components P hP := by
      intro j
      exact ⟨((cd_j j).2 : AffineCoordinateRingBar X), hdP j,
        ⟨(cd_j j).1, ((hcd_j j).symm.trans (mul_comm _ _))⟩⟩

    have hf_vanish : MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) f = 0 :=
      hf _ (φ.image_mem P hP hreg_comp)

    obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ := h_clearing P hP hreg_comp f

    rw [hf_vanish, zero_mul] at hf₀_eval


    have h_cross : f₀ * b_r = g₀ * a_r := by
      apply IsFractionRing.injective (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))
      simp only [map_mul]
      calc _ = (algebraMap _ _ g₀ * dominantPullbackSubstHom φ.components f) *
                algebraMap _ _ b_r := by rw [hf₀_eq]
        _ = algebraMap _ _ g₀ * (dominantPullbackSubstHom φ.components f *
                algebraMap _ _ b_r) := by ring
        _ = algebraMap _ _ g₀ * algebraMap _ _ a_r := by rw [hab_r]
    have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP b_r =
        evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP a_r := by
      rw [← map_mul, ← map_mul, h_cross]

    rw [hf₀_eval.symm, zero_mul] at h_eval_cross
    have haP : evalBarAtPoint k X P hP a_r = 0 := by
      rcases mul_eq_zero.mp h_eval_cross.symm with hg₀P | haP
      · exact absurd hg₀P hg₀_ne
      · exact haP
    simp [haP]

  have hprod_zero : product = 0 := by
    obtain ⟨f_poly, hf_poly⟩ := Ideal.Quotient.mk_surjective product
    suffices h_mem : f_poly ∈ idealOfAlgebraicSet X by
      rw [← hf_poly]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
    rw [mem_idealOfAlgebraicSet_iff]
    intro P hP
    have := hprod_vanishes P hP
    rw [← hf_poly, evalBarAtPoint_mk] at this
    exact this
  exact hprod_ne hprod_zero

end Theorem158

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Def.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part6
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ghsiOutFieldWeight_split (hf : V → ℝ) (q a : ConfigSpace V) :
    ghsiOutFieldWeight hf q a =
      ghsiOutFieldWeight hf q (ghsLUComplete q (ghsLSplitEquiv q a).2) := by
  unfold ghsiOutFieldWeight
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  have hq : ¬ q v = true := by simpa using (Finset.mem_compl.mp hv)
  congr 1
  unfold spin
  rw [ghsLUComplete_eq_on q a hq]

theorem ghsi_wJ_field_eq_tWeight_mul_out (K : Sym2 V → ℝ) (hf : V → ℝ)
    (q a : ConfigSpace V) :
    wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) a =
      ghsiTWeight G K hf q a * ghsiOutFieldWeight hf q a := by
  unfold wJ ghsiTWeight ghsiOutFieldWeight
  rw [← Real.exp_add]
  congr 1
  have hsplit : (∑ v : V, (2 * hf v) * spin a v) =
      (∑ v ∈ ghsLAgreeFinset q, (2 * hf v) * spin a v) +
        ∑ v ∈ (ghsLAgreeFinset q)ᶜ, (2 * hf v) * spin a v := by
    calc
      (∑ v : V, (2 * hf v) * spin a v) =
          ∑ v ∈ ghsLAgreeFinset q ∪ (ghsLAgreeFinset q)ᶜ,
            (2 * hf v) * spin a v := by rw [Finset.union_compl]
      _ = _ := Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro v hvA hvAc
        exact (Finset.mem_compl.mp hvAc) hvA)
  rw [hsplit]
  ring

theorem ghsiFibreT_eq_agreementMag (K : Sym2 V → ℝ) (hf : V → ℝ)
    (y : V) (q : ConfigSpace V) :
    ghsiFibreT G K hf y q =
      ghsiAgreementMag G K hf y (ghsLAgreeFinset q) := by
  rw [ghsiFibreT_eq_tExpectation]
  by_cases hy : y ∈ ghsLAgreeFinset q
  · have hqy : q y = true := (mem_ghsLAgreeFinset q y).mp hy
    unfold ghsiAgreementMag ghsvp_vertexCorrField expJ
    rw [if_pos hy]
    let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      ghsiTWeight G K hf q (ghsLTComplete q st)
    let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
      spin (ghsLTComplete q st) y
    let gO : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
      ghsiOutFieldWeight hf q (ghsLUComplete q su)
    have htvar (a : ConfigSpace V) : tvar a (ghsLMate q a) y = spin a y := by
      rw [ghsL_tvar_mate, if_pos hqy]
    have htlocal (a : ConfigSpace V) : spin a y = tObs (ghsLSplitEquiv q a).1 := by
      unfold tObs spin
      rw [ghsLTComplete_eq_on q a hqy]
    have hbase (a : ConfigSpace V) : ghsiTWeight G K hf q a =
        fT (ghsLSplitEquiv q a).1 := by rw [ghsiTWeight_split]
    have hout (a : ConfigSpace V) : ghsiOutFieldWeight hf q a =
        gO (ghsLSplitEquiv q a).2 := by rw [ghsiOutFieldWeight_split]
    have hcross := ghsL_split_cross_product (V := V) q
      (fun st => fT st * tObs st) fT (fun _ => (1 : ℝ)) gO
    unfold ghsiTExpectation
    have hzt : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) ≠ 0 :=
      (Finset.sum_pos (fun a _ => ghsiTWeight_pos G K hf q a)
        Finset.univ_nonempty).ne'
    have hza : ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) ≠ 0 := (ZJ_pos _ _ _).ne'
    field_simp [hzt, hza]
    have hL1 : (∑ a : ConfigSpace V,
        ghsiTWeight G K hf q a * tvar a (ghsLMate q a) y) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase, htvar, htlocal]
      ring
    have hL0 : (∑ a : ConfigSpace V, ghsiTWeight G K hf q a) =
        ∑ a : ConfigSpace V, fT (ghsLSplitEquiv q a).1 * (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hbase]
      ring
    have hR1 : (∑ a : ConfigSpace V, spinProd {y} a *
        wJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
          (fun e => 2 * K e) (fun x => 2 * hf x) a) =
        ∑ a : ConfigSpace V,
          (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
            gO (ghsLSplitEquiv q a).2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsi_wJ_field_eq_tWeight_mul_out, hbase, hout]
      simp only [spinProd, Finset.prod_singleton]
      rw [htlocal]
      ring
    have hR0 : ZJ (ghsvp_vertexEdges G.edgeFinset (ghsLAgreeFinset q))
        (fun e => 2 * K e) (fun x => 2 * hf x) =
        ∑ a : ConfigSpace V,
          fT (ghsLSplitEquiv q a).1 * gO (ghsLSplitEquiv q a).2 := by
      unfold ZJ
      apply Finset.sum_congr rfl
      intro a _
      rw [ghsi_wJ_field_eq_tWeight_mul_out, hbase, hout]
    rw [hL1, hL0, hR1, hR0]
    simpa [mul_comm] using hcross
  · have hqy : ¬ q y = true := fun h => hy ((mem_ghsLAgreeFinset q y).mpr h)
    unfold ghsiAgreementMag ghsiTExpectation
    rw [if_neg hy]
    simp_rw [ghsL_tvar_mate, if_neg hqy, mul_zero]
    simp


theorem ghsiExp2_fibre (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf F =
      ∑ q : ConfigSpace V,
        ghsiAgreementProb G K hf q * ghsiFibreExpectation G K hf F q := by
  unfold ghsiExp2
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  have hm' : (∑ a : ConfigSpace V,
      wJ G.edgeFinset K hf a * wJ G.edgeFinset K hf (ghsLMate q a)) ≠ 0 := by
    simpa [ghsiFibreMass, ghsiFibreWeight] using hm
  have hZ : ZJ G.edgeFinset K hf ≠ 0 := (ZJ_pos _ _ _).ne'
  unfold ghsiAgreementProb ghsiFibreExpectation ghsiFibreNumerator ghsiFibreMass
    ghsiFibreWeight
  field_simp [hm, hm', hZ]

theorem ghsi_fibreFactorization (K : Sym2 V → ℝ) (hf : V → ℝ)
    (o x y : V) (q : ConfigSpace V) :
    ghsiFibreExpectation G K hf
        (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ghsiFibreUU G K hf o x q * ghsiFibreT G K hf y q := by
  let fT : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    ghsiTWeight G K hf q (ghsLTComplete q st)
  let fU : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    ghsiUWeight G K q (ghsLUComplete q su)
  let tObs : ((v : {v : V // q v = true}) → Bool) → ℝ := fun st =>
    tvar (ghsLTComplete q st) (ghsLMate q (ghsLTComplete q st)) y
  let uuObs : ((v : {v : V // ¬ q v = true}) → Bool) → ℝ := fun su =>
    uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) o *
      uvar (ghsLUComplete q su) (ghsLMate q (ghsLUComplete q su)) x
  have hweight (a : ConfigSpace V) : ghsiFibreWeight G K hf q a =
      fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreWeight
    rw [ghsi_duplicateWeight_eq_tWeight_mul_uWeight,
      ghsiTWeight_split, ghsiUWeight_split]
  have htobs (a : ConfigSpace V) : tvar a (ghsLMate q a) y =
      tObs (ghsLSplitEquiv q a).1 := ghsL_tvar_split q a y
  have huuobs (a : ConfigSpace V) :
      uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x =
        uuObs (ghsLSplitEquiv q a).2 := ghsL_uvar_mul_split q a o x
  have hUUT : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x * tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x *
        tvar a (ghsLMate q a) y) = _
    rw [hweight, htobs, huuobs]
    ring
  have hMass : ghsiFibreMass G K hf q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 * fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreMass
    exact Finset.sum_congr rfl (fun a _ => hweight a)
  have hT : ghsiFibreNumerator G K hf (fun a b => tvar a b y) q =
      ∑ a : ConfigSpace V,
        (fT (ghsLSplitEquiv q a).1 * tObs (ghsLSplitEquiv q a).1) *
          fU (ghsLSplitEquiv q a).2 := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a * tvar a (ghsLMate q a) y = _
    rw [hweight, htobs]
    ring
  have hUU : ghsiFibreNumerator G K hf
      (fun a b => uvar a b o * uvar a b x) q =
      ∑ a : ConfigSpace V,
        fT (ghsLSplitEquiv q a).1 *
          (fU (ghsLSplitEquiv q a).2 * uuObs (ghsLSplitEquiv q a).2) := by
    unfold ghsiFibreNumerator
    apply Finset.sum_congr rfl
    intro a _
    change ghsiFibreWeight G K hf q a *
      (uvar a (ghsLMate q a) o * uvar a (ghsLMate q a) x) = _
    rw [hweight, huuobs]
    ring
  have hcross := ghsL_split_cross_product (V := V) q
    (fun st => fT st * tObs st) fT
    (fun su => fU su * uuObs su) fU
  unfold ghsiFibreUU ghsiFibreT ghsiFibreExpectation
  have hm : ghsiFibreMass G K hf q ≠ 0 := (ghsiFibreMass_pos G K hf q).ne'
  field_simp [hm]
  rw [hUUT, hMass, hUU, hT]
  simpa [mul_comm] using hcross

theorem ghsi_duplicate_cov_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x * tvar a b y) ≤
      ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) *
        ghsiExp2 G K hf (fun a b => tvar a b y) := by
  have hfkg := ghsL_fkg_antitone_monotone
    (ghsiAgreementProb_nonneg G K hf) (ghsiAgreementProb_sum_eq_one G K hf)
    (ghsiAgreementProb_fkg G K hf hK hhf)
    (show Antitone (ghsiFibreUU G K hf o x) from by
      intro q r hqr
      rw [ghsiFibreUU_eq_disagreementCorr G K hf o x hox,
        ghsiFibreUU_eq_disagreementCorr G K hf o x hox]
      exact ghsiDisagreementCorr_antitone G K hK o x
        (ghsLAgreeFinset_monotone hqr))
    (show Monotone (ghsiFibreT G K hf y) from by
      intro q r hqr
      rw [ghsiFibreT_eq_agreementMag G K hf y,
        ghsiFibreT_eq_agreementMag G K hf y]
      exact ghsiAgreementMag_monotone G K hf hK hhf y
        (ghsLAgreeFinset_monotone hqr))
  rw [ghsiExp2_fibre, ghsiExp2_fibre, ghsiExp2_fibre]
  simp_rw [ghsi_fibreFactorization G K hf o x y]
  exact hfkg

theorem ghsiExp2_add (K : Sym2 V → ℝ) (hf : V → ℝ)
    (F H : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a b => F a b + H a b) =
      ghsiExp2 G K hf F + ghsiExp2 G K hf H := by
  unfold ghsiExp2
  rw [← add_div]
  congr 1
  simp_rw [mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]

theorem ghsiExp2_const_mul (K : Sym2 V → ℝ) (hf : V → ℝ) (c : ℝ)
    (F : ConfigSpace V → ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a b => c * F a b) = c * ghsiExp2 G K hf F := by
  unfold ghsiExp2
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem expJ_one (K : Sym2 V → ℝ) (hf : V → ℝ) :
    expJ G.edgeFinset K hf (fun _ => (1 : ℝ)) = 1 := by
  unfold expJ
  have hnum : (∑ s : ConfigSpace V, (1 : ℝ) * wJ G.edgeFinset K hf s) =
      ZJ G.edgeFinset K hf := by simp [ZJ]
  rw [hnum]
  exact div_self (ZJ_pos _ _ _).ne'

theorem ghsiExp2_factor_a (K : Sym2 V → ℝ) (hf : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun a _ => f a) = expJ G.edgeFinset K hf f := by
  have h := ghsiExp2_factor G K hf f (fun _ => (1 : ℝ))
  simpa [expJ_one G K hf] using h

theorem ghsiExp2_factor_b (K : Sym2 V → ℝ) (hf : V → ℝ)
    (f : ConfigSpace V → ℝ) :
    ghsiExp2 G K hf (fun _ b => f b) = expJ G.edgeFinset K hf f := by
  have h := ghsiExp2_factor G K hf (fun _ => (1 : ℝ)) f
  simpa [expJ_one G K hf] using h


theorem ghsi_ursell_eq_four_duplicate_cov
    (K : Sym2 V → ℝ) (hf : V → ℝ) (o x y : V) :
    expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x * spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s y) *
            expJ G.edgeFinset K hf (fun s => spin s x) +
          2 * expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) =
      4 * (ghsiExp2 G K hf
              (fun a b => uvar a b o * uvar a b x * tvar a b y) -
            ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) *
              ghsiExp2 G K hf (fun a b => tvar a b y)) := by
  have hthree :
      (fun a b => uvar a b o * uvar a b x * tvar a b y) =
        (fun a b =>
          (1 / 8 : ℝ) * (spin a o * (spin a x * spin a y)) +
          (1 / 8 : ℝ) * ((spin a o * spin a x) * spin b y) +
          (-1 / 8 : ℝ) * ((spin a o * spin a y) * spin b x) +
          (-1 / 8 : ℝ) * (spin a o * (spin b x * spin b y)) +
          (-1 / 8 : ℝ) * ((spin a x * spin a y) * spin b o) +
          (-1 / 8 : ℝ) * (spin a x * (spin b o * spin b y)) +
          (1 / 8 : ℝ) * (spin a y * (spin b o * spin b x)) +
          (1 / 8 : ℝ) * (spin b o * (spin b x * spin b y))) := by
    funext a b
    simp only [uvar, tvar]
    ring
  rw [hthree]
  simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
    ghsiExp2_factor_a, ghsiExp2_factor_b]
  have huu : ghsiExp2 G K hf (fun a b => uvar a b o * uvar a b x) =
      (expJ G.edgeFinset K hf (fun s => spin s o * spin s x) -
        expJ G.edgeFinset K hf (fun s => spin s o) *
          expJ G.edgeFinset K hf (fun s => spin s x)) / 2 := by
    have hexp : (fun a b => uvar a b o * uvar a b x) =
        (fun a b =>
          (1 / 4 : ℝ) * (spin a o * spin a x) +
          (-1 / 4 : ℝ) * (spin a o * spin b x) +
          (-1 / 4 : ℝ) * (spin a x * spin b o) +
          (1 / 4 : ℝ) * (spin b o * spin b x)) := by
      funext a b
      simp only [uvar]
      ring
    rw [hexp]
    simp only [ghsiExp2_add, ghsiExp2_const_mul, ghsiExp2_factor,
      ghsiExp2_factor_a, ghsiExp2_factor_b]
    ring
  have ht : ghsiExp2 G K hf (fun a b => tvar a b y) =
      expJ G.edgeFinset K hf (fun s => spin s y) := by
    have hexp : (fun a b => tvar a b y) =
        (fun a b => (1 / 2 : ℝ) * spin a y + (1 / 2 : ℝ) * spin b y) := by
      funext a b
      simp only [tvar]
      ring
    rw [hexp]
    simp only [ghsiExp2_add, ghsiExp2_const_mul,
      ghsiExp2_factor_a, ghsiExp2_factor_b]
    ring
  rw [huu, ht]
  ring


theorem ghsi_ursell_nonpos (K : Sym2 V → ℝ) (hf : V → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hhf : ∀ x, 0 ≤ hf x)
    (o x y : V) (hox : o ≠ x) :
    expJ G.edgeFinset K hf (fun s => spin s o * (spin s x * spin s y)) -
          expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x * spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) -
          expJ G.edgeFinset K hf (fun s => spin s o * spin s y) *
            expJ G.edgeFinset K hf (fun s => spin s x) +
          2 * expJ G.edgeFinset K hf (fun s => spin s o) *
            expJ G.edgeFinset K hf (fun s => spin s x) *
            expJ G.edgeFinset K hf (fun s => spin s y) ≤ 0 := by
  rw [ghsi_ursell_eq_four_duplicate_cov]
  have h := ghsi_duplicate_cov_nonpos G K hf hK hhf o x y hox
  linarith


end StatMech.Ising

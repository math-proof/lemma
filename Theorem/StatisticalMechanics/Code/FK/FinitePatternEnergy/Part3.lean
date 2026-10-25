/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FinitePatternEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part2
open MeasureTheory Finset


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {C}


variable (C : SimpleGraph V) [DecidableRel C.Adj]


variable {C}


omit [Fintype V] in
theorem setPattern_mem_patternEvent (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : setPattern I eta psi ∈ patternEvent I eta := by
  funext e
  simp [Finset.restrict, setPattern]

omit [Fintype V] in
theorem agreesOff_setPattern (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : AgreesOff I psi (setPattern I eta psi) := by
  intro e he
  exact setPattern_of_not_mem eta he psi

omit [Fintype V] in
theorem eq_setPattern_of_agreesOff_of_mem_pattern
    {I : Finset (Sym2 V)} {eta : ConfigSpace ↥I}
    {psi omega : ConfigSpace (Sym2 V)}
    (hoff : AgreesOff I psi omega) (hpat : omega ∈ patternEvent I eta) :
    omega = setPattern I eta psi := by
  funext e
  by_cases he : e ∈ I
  · have hcoord := congrFun hpat ⟨e, he⟩
    simpa [patternEvent, Finset.restrict, setPattern, he] using hcoord
  · rw [setPattern_of_not_mem eta he psi]
    exact hoff e he

omit [Fintype V] in

theorem setPattern_eq_self_of_mem_pattern
    {I : Finset (Sym2 V)} {eta : ConfigSpace ↥I}
    {omega : ConfigSpace (Sym2 V)} (hpat : omega ∈ patternEvent I eta) :
    setPattern I eta omega = omega := by
  symm
  exact eq_setPattern_of_agreesOff_of_mem_pattern (agreesOff_self I omega) hpat

omit [Fintype V] in


theorem dependsOnOutside_preimage_setPattern
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (A : Set (ConfigSpace (Sym2 V))) :
    DependsOnOutside I (setPattern I eta ⁻¹' A) := by
  intro psi rho hoff
  have heq : setPattern I eta psi = setPattern I eta rho := by
    funext e
    by_cases he : e ∈ I
    · rw [setPattern_of_mem eta he, setPattern_of_mem eta he]
    · rw [setPattern_of_not_mem eta he, setPattern_of_not_mem eta he]
      exact (hoff e he).symm
  simp only [Set.mem_preimage]
  rw [heq]


theorem cFE_pow_le_condBcProb_pattern
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card ≤
      ∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega := by
  classical
  let target := setPattern I eta psi
  have htOff : AgreesOff I psi target := agreesOff_setPattern I eta psi
  have htPat : target ∈ patternEvent I eta := setPattern_mem_patternEvent I eta psi
  have hsingle :
      (∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega) = condBcProb G C p q I psi target := by
    have hind : (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target = 1 :=
      Set.indicator_of_mem htPat _
    calc
      (∑ omega, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condBcProb G C p q I psi omega) =
          (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target *
            condBcProb G C p q I psi target := by
        apply Finset.sum_eq_single target
        · intro omega _ hne
          by_cases hoff : AgreesOff I psi omega
          · have hnpat : omega ∉ patternEvent I eta := by
              intro hpat
              exact hne (eq_setPattern_of_agreesOff_of_mem_pattern hoff hpat)
            rw [Set.indicator_of_notMem hnpat, zero_mul]
          · unfold condBcProb
            rw [if_neg hoff, mul_zero]
        · simp
      _ = condBcProb G C p q I psi target := by rw [hind, one_mul]
  rw [hsingle]
  unfold condBcProb
  rw [if_pos htOff, le_div_iff₀
    (inducedBcZ_pos G C hp hp1 (zero_lt_one.trans_le hq) I psi)]
  simpa [target] using cFE_pow_mul_inducedBcZ_le_setPattern G C hp hp1 hq I eta psi


theorem cFE_pow_mul_condFibreMass_le_pattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card * (∑ omega ∈ condFibre I psi, fkProb G p q omega) ≤
      fkProb G p q (setPattern I eta psi) := by
  have hZ : 0 < fkZ G p q := fkZ_pos G hp hp1 (zero_lt_one.trans_le hq)
  have hweights :
      (∑ omega ∈ condFibre I psi, fkWeight G p q omega) =
        agreeWeightSum G p q I psi := by
    apply Finset.sum_congr
    · ext omega
      simp only [mem_condFibre, Finset.mem_filter, Finset.mem_univ, true_and,
        AgreesOff]
    · intro omega _
      rfl
  unfold fkProb
  rw [← Finset.sum_div, ← mul_div_assoc, hweights]
  exact div_le_div_of_nonneg_right
    (cFE_pow_mul_agreeWeightSum_le_setPattern G hp hp1 hq I eta psi) hZ.le


theorem cFE_pow_le_condFkProb_pattern
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) (psi : ConfigSpace (Sym2 V)) :
    cFE p q ^ I.card ≤
      ∑ omega ∈ condFibre I psi, (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condFkProb G p q I psi omega := by
  classical
  let target := setPattern I eta psi
  have htF : target ∈ condFibre I psi := by
    rw [mem_condFibre]
    exact agreesOff_setPattern I eta psi
  have htP : target ∈ patternEvent I eta := setPattern_mem_patternEvent I eta psi
  have hmass : 0 < ∑ omega ∈ condFibre I psi, fkProb G p q omega := by
    exact Finset.sum_pos (fun omega _ => fkProb_pos G hp hp1
      (zero_lt_one.trans_le hq) omega) ⟨target, htF⟩
  have hsingle :
      (∑ omega ∈ condFibre I psi,
        (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
        condFkProb G p q I psi omega) = condFkProb G p q I psi target := by
    have hind : (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target = 1 :=
      Set.indicator_of_mem htP _
    calc
      (∑ omega ∈ condFibre I psi,
        (patternEvent I eta).indicator (fun _ => (1 : ℝ)) omega *
          condFkProb G p q I psi omega) =
          (patternEvent I eta).indicator (fun _ => (1 : ℝ)) target *
            condFkProb G p q I psi target := by
        apply Finset.sum_eq_single target
        · intro omega hoff hne
          rw [mem_condFibre] at hoff
          have hnpat : omega ∉ patternEvent I eta := by
            intro hpat
            exact hne (eq_setPattern_of_agreesOff_of_mem_pattern hoff hpat)
          rw [Set.indicator_of_notMem hnpat, zero_mul]
        · exact fun hnot => (hnot htF).elim
      _ = condFkProb G p q I psi target := by rw [hind, one_mul]
  rw [hsingle]
  unfold condFkProb
  rw [le_div_iff₀ hmass]
  simpa [target] using cFE_pow_mul_condFibreMass_le_pattern G hp hp1 hq I eta psi


theorem fkProb_eq_fibreMass_mul_condFkProb_general
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (I : Finset (Sym2 V)) (omega : ConfigSpace (Sym2 V)) :
    fkProb G p q omega =
      (∑ rho ∈ condFibre I omega, fkProb G p q rho) *
        condFkProb G p q I omega omega := by
  have hpos : 0 < ∑ rho ∈ condFibre I omega, fkProb G p q rho :=
    Finset.sum_pos (fun rho _ => fkProb_pos G hp hp1 hq rho)
      ⟨omega, self_mem_condFibre I omega⟩
  unfold condFkProb
  field_simp


theorem fkProb_fibre_decompose_general
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (I : Finset (Sym2 V)) (B : Set (ConfigSpace (Sym2 V))) :
    (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) =
      ∑ psi ∈ fibreReps I,
        (∑ sigma ∈ condFibre I psi, fkProb G p q sigma) *
          (∑ rho ∈ condFibre I psi,
            B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := projOff I) (t := fibreReps I)
    (fun omega _ => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, projOff_idem I omega⟩)]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [fibreReps, Finset.mem_filter] at hpsi
  rw [show (Finset.univ.filter (fun rho => projOff I rho = psi)) = condFibre I psi from
    filter_projOff_eq_condFibre I psi hpsi.2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hfac := fkProb_eq_fibreMass_mul_condFkProb_general G hp hp1 hq I rho
  have hfib : condFibre I rho = condFibre I psi := by
    exact condFibre_congr_dom' (agreesOff_symm hrho)
  rw [hfib] at hfac
  have hcond : condFkProb G p q I rho rho = condFkProb G p q I psi rho := by
    unfold condFkProb
    rw [hfib]
  rw [hfac, hcond]
  ring


theorem condFkProb_sum_outside
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {I : Finset (Sym2 V)} {B : Set (ConfigSpace (Sym2 V))}
    (hB : DependsOnOutside I B) (psi : ConfigSpace (Sym2 V)) :
    (∑ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
      B.indicator (fun _ => (1 : ℝ)) psi := by
  have hconst : ∀ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho = B.indicator (fun _ => (1 : ℝ)) psi := by
    intro rho hrho
    rw [mem_condFibre] at hrho
    exact indicator_const_on_fibre hB hrho
  calc
    (∑ rho ∈ condFibre I psi,
      B.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
        B.indicator (fun _ => (1 : ℝ)) psi *
          ∑ rho ∈ condFibre I psi, condFkProb G p q I psi rho := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun rho hrho => by rw [hconst rho hrho])
    _ = B.indicator (fun _ => (1 : ℝ)) psi := by
      rw [condFkProb_sum_eq_one G hp hp1 hq I psi, mul_one]


theorem condFkProb_cross_outside
    {p q : ℝ} {I : Finset (Sym2 V)}
    {A B : Set (ConfigSpace (Sym2 V))} (hB : DependsOnOutside I B)
    (psi : ConfigSpace (Sym2 V)) :
    (∑ rho ∈ condFibre I psi,
      (A ∩ B).indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) =
      B.indicator (fun _ => (1 : ℝ)) psi *
        (∑ rho ∈ condFibre I psi,
          A.indicator (fun _ => (1 : ℝ)) rho * condFkProb G p q I psi rho) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hBeq : psi ∈ B ↔ rho ∈ B := hB psi rho hrho
  by_cases hA : rho ∈ A <;> by_cases hBrho : rho ∈ B <;>
    simp [Set.indicator, hA, hBrho, hBeq, Set.mem_inter_iff]


theorem cFE_pow_mul_event_le_pattern_inter
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (B : Set (ConfigSpace (Sym2 V))) (hB : DependsOnOutside I B) :
    cFE p q ^ I.card *
        (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * fkProb G p q omega) ≤
      ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega *
        fkProb G p q omega := by
  rw [fkProb_fibre_decompose_general G hp hp1 (zero_lt_one.trans_le hq) I B,
    fkProb_fibre_decompose_general G hp hp1 (zero_lt_one.trans_le hq) I
      (patternEvent I eta ∩ B), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  have hfm : 0 ≤ ∑ sigma ∈ condFibre I psi, fkProb G p q sigma :=
    Finset.sum_nonneg (fun sigma _ => fkProb_nonneg G hp hp1
      (zero_lt_one.trans_le hq) sigma)
  rw [condFkProb_sum_outside G hp hp1 (zero_lt_one.trans_le hq) hB psi,
    condFkProb_cross_outside G hB psi]
  have hpat := cFE_pow_le_condFkProb_pattern G hp hp1 hq I eta psi
  by_cases hpsiB : psi ∈ B
  · rw [Set.indicator_of_mem hpsiB]
    nlinarith [mul_le_mul_of_nonneg_left hpat hfm]
  · rw [Set.indicator_of_notMem hpsiB]
    simp


theorem cFE_pow_mul_bcEvent_le_pattern_inter
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (B : Set (ConfigSpace (Sym2 V))) (hB : DependsOnOutside I B) :
    cFE p q ^ I.card *
        (∑ omega, B.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega) ≤
      ∑ omega, (patternEvent I eta ∩ B).indicator (fun _ => (1 : ℝ)) omega *
        bcProb G C p q omega := by
  classical
  rw [bcProb_fibre_decompose G C hp hp1 (zero_lt_one.trans_le hq) I B,
    bcProb_fibre_decompose G C hp hp1 (zero_lt_one.trans_le hq) I
      (patternEvent I eta ∩ B), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro psi hpsi
  rw [fibreReps, Finset.mem_filter] at hpsi
  have hfm : 0 ≤ ∑ sigma ∈ condFibre I psi, bcProb G C p q sigma :=
    Finset.sum_nonneg (fun sigma _ =>
      bcProb_nonneg G C hp hp1 (zero_lt_one.trans_le hq) sigma)
  rw [condBcProb_sum_outside G C hp hp1 (zero_lt_one.trans_le hq) hB hpsi.2,
    condBcProb_cross_outside G C hB]
  have hpat := cFE_pow_le_condBcProb_pattern G C hp hp1 hq I eta psi
  by_cases hpsiB : psi ∈ B
  · rw [Set.indicator_of_mem hpsiB]
    nlinarith [mul_le_mul_of_nonneg_left hpat hfm]
  · rw [Set.indicator_of_notMem hpsiB]
    simp


theorem cFE_pow_mul_bcPreimage_le_event
    (C : SimpleGraph V) [DecidableRel C.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (A : Set (ConfigSpace (Sym2 V))) :
    cFE p q ^ I.card *
        (∑ omega, (setPattern I eta ⁻¹' A).indicator (fun _ => (1 : ℝ)) omega *
          bcProb G C p q omega) ≤
      ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * bcProb G C p q omega := by
  let B := setPattern I eta ⁻¹' A
  have hins : patternEvent I eta ∩ B ⊆ A := by
    rintro omega ⟨hpat, hB⟩
    change setPattern I eta omega ∈ A at hB
    rwa [setPattern_eq_self_of_mem_pattern hpat] at hB
  refine (cFE_pow_mul_bcEvent_le_pattern_inter G C hp hp1 hq I eta B
    (dependsOnOutside_preimage_setPattern I eta A)).trans ?_
  apply Finset.sum_le_sum
  intro omega _
  by_cases hmem : omega ∈ patternEvent I eta ∩ B
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hins hmem)]
  · rw [Set.indicator_of_notMem hmem]
    rw [zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
      (bcProb_nonneg G C hp hp1 (zero_lt_one.trans_le hq) omega)

end FK
end StatMech

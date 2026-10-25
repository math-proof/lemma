/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Mathlib.MeasureTheory.Measure.Portmanteau
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolumePhaseTransport
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

theorem pottsColorEvent_isClopen (d q : Nat) (x : Site d) (b : Fin q) :
    IsClopen (pottsColorEvent d q x b) := by
  change IsClopen ((fun sigma : PottsConfig d q => sigma x) ⁻¹' {b})
  exact IsClopen.preimage (isClopen_discrete _)
    (continuous_apply x : Continuous
      (fun sigma : PottsConfig d q => sigma x))


theorem wiredPottsFiniteMeasure_real_pottsColorEvent_origin
    (d n q : Nat) [NeZero q] (b : Fin q) (beta J : Real) :
    ((wiredPottsFiniteMeasure d n q b beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b) =
      pottsBoundaryProbWired (boxGraph d n) (boxBoundary d n)
        q b beta J (boxOrigin d n) := by
  classical
  let E : Set (boxVerts d n -> Fin q) :=
    {sigma | sigma (boxOrigin d n) = b}
  have hpre : ivp_extendSpin d n q ⁻¹'
      pottsColorEvent d q (origin d) b = E := by
    ext sigma
    simp only [Set.mem_preimage, pottsColorEvent, Set.mem_setOf_eq, E]
    unfold ivp_extendSpin
    rw [dif_pos (origin_mem_box_boxVerts d n)]
    rfl
  have hmeas : MeasurableSet (pottsColorEvent d q (origin d) b) :=
    (pottsColorEvent_isClopen d q (origin d) b).2.measurableSet
  change ((Measure.map (ivp_extendSpin d n q)
    (wiredPottsPMF (boxGraph d n) (boxBoundary d n)
      q b beta J).toMeasure) (pottsColorEvent d q (origin d) b)).toReal = _
  rw [Measure.map_apply (ivp_measurable_extendSpin d n q) hmeas, hpre]
  unfold wiredPottsPMF pottsBoundaryProbWired
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun sigma _ => ?_)]
  · apply Finset.sum_congr rfl
    intro sigma _
    by_cases hsigma : sigma (boxOrigin d n) = b
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply,
        ENNReal.toReal_ofReal
          (pottsProbWired_nonneg (boxGraph d n) (boxBoundary d n)
            q b beta J sigma)]
      simp [hsigma]
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp [hsigma]
  · by_cases hsigma : sigma (boxOrigin d n) = b
    · have hmem : sigma ∈ E := hsigma
      rw [Set.indicator_of_mem hmem, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · have hmem : sigma ∉ E := hsigma
      rw [Set.indicator_of_notMem hmem]
      simp


theorem wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection
    (d n q : Nat) [NeZero q] (hd : 1 <= d) (hn : 1 <= n)
    (hq : 2 <= q) (b : Fin q) (beta J : Real)
    (hbeta : 0 < beta) (hJ : 0 < J) :
    ((wiredPottsFiniteMeasure d n q b beta J :
        ProbabilityMeasure (PottsConfig d q)) :
      Measure (PottsConfig d q)).real
          (pottsColorEvent d q (origin d) b) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        ((wiredFiniteMeasure d n
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d n) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hq0 : (0 : Real) < q := by
    exact_mod_cast (show 0 < q by omega)
  obtain ⟨v0, hv0⟩ := boxBoundary_nonempty d n hd hn
  rw [wiredPottsFiniteMeasure_real_pottsColorEvent_origin]
  rw [pottsBoundaryProbWired_sub_inv_eq_conn
    (boxGraph d n) (boxBoundary d n) q b beta J
    (boxOrigin d n) v0 hv0]
  rw [wiredConnToBdryProbQ_eq_wiredFkProb_sum]
  let S : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
    {omega | ConnToBdry (boxGraph d n) (boxBoundary d n) omega
      (boxOrigin d n)}
  have hmass := fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) n hp hp1 hq0 S
      (measurableSet_boxBdryConnEvent d n)
  have hsum :
      (∑ omega ∈ Finset.univ.filter
          (fun omega : ConfigSpace (Sym2 (boxVerts d n)) =>
            ConnToBdry (boxGraph d n) (boxBoundary d n) omega
              (boxOrigin d n)),
        wiredFkProb (boxGraph d n) (boxBoundary d n) p (q : Real) omega) =
      ∑ omega : ConfigSpace (Sym2 (boxVerts d n)),
        S.indicator (fun _ => (1 : Real)) omega *
          wiredFkProb (boxGraph d n) (boxBoundary d n) p (q : Real) omega := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro omega _
    by_cases homega : ConnToBdry (boxGraph d n) (boxBoundary d n) omega
        (boxOrigin d n)
    · have hmem : omega ∈ S := homega
      simp [homega, Set.indicator_of_mem hmem]
    · have hmem : omega ∉ S := homega
      simp [homega, Set.indicator_of_notMem hmem]
  rw [hsum, <- hmass]
  rfl


theorem wiredPottsLimit_colorBias_eq_fkTheta
    (d q : Nat) [NeZero q] (hd : 1 <= d) (hq : 2 <= q)
    (b : Fin q) (beta J : Real) (hbeta : 0 < beta) (hJ : 0 < J)
    (mu : ProbabilityMeasure (PottsConfig d q)) (phi : Nat -> Nat)
    (hphi : StrictMono phi)
    (hmu : Tendsto
      (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
      atTop (nhds mu)) :
    ((mu : Measure (PottsConfig d q)).real
        (pottsColorEvent d q (origin d) b)) - 1 / (q : Real) =
      ((q : Real) - 1) / q *
        fkTheta d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by linarith [Real.exp_pos (-(beta * J))])
          (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)
          (q := q) := by
  let p : Real := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-(beta * J))]
  have hq1 : (1 : Real) <= q := by exact_mod_cast (show 1 <= q by omega)
  have hq0 : (0 : Real) < q := zero_lt_one.trans_le hq1
  let A := pottsColorEvent d q (origin d) b
  have hA : IsClopen A := pottsColorEvent_isClopen d q (origin d) b
  have hcolorNN :=
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hmu hA
  have hcolor : Tendsto
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A)
      atTop (nhds ((mu : Measure _).real A)) := by
    simpa [Measure.real] using
      NNReal.continuous_coe.continuousAt.tendsto.comp hcolorNN
  have hconn := (fkgq_boxBdryConnEvent_diag_tendsto
    (d := d) hp hp1 hq1).comp hphi.tendsto_atTop
  have heq : ∀ᶠ n : Nat in atTop,
      ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A -
          1 / (q : Real) =
        ((q : Real) - 1) / q *
          ((wiredFiniteMeasure d (phi n) hp hp1 hq0 :
            ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
              (boxBdryConnEvent d (phi n)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa [A, p] using
      wiredPottsFiniteMeasure_colorBias_eq_boundaryConnection
        d (phi n) q hd (le_trans hn (hphi.id_le n)) hq b beta J hbeta hJ
  have hleft := hcolor.sub (tendsto_const_nhds :
    Tendsto (fun _ : Nat => 1 / (q : Real)) atTop (nhds (1 / (q : Real))))
  have hright := (tendsto_const_nhds : Tendsto
      (fun _ : Nat => ((q : Real) - 1) / q) atTop
        (nhds (((q : Real) - 1) / q))).mul hconn
  have heq' :
      (fun n => ((wiredPottsFiniteMeasure d (phi n) q b beta J :
        ProbabilityMeasure (PottsConfig d q)) : Measure _).real A -
          1 / (q : Real)) =ᶠ[atTop]
      (fun n => ((q : Real) - 1) / q *
        ((wiredFiniteMeasure d (phi n) hp hp1 hq0 :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure _).real
            (boxBdryConnEvent d (phi n))) := heq
  exact tendsto_nhds_unique hleft
    (hright.congr' (Filter.EventuallyEq.symm heq'))


theorem Potts.monoIndicator_relabel
    {V : Type*} {q : Nat} (e : Fin q ≃ Fin q)
    (sigma : V -> Fin q) (edge : Sym2 V) :
    Potts.monoIndicator (fun x => e (sigma x)) edge =
      Potts.monoIndicator sigma edge := by
  induction edge with
  | _ x y => simp [Potts.monoIndicator_mk]


theorem Potts.pottsProb_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : Nat} [NeZero q] (e : Fin q ≃ Fin q)
    (beta J : Real) (sigma : V -> Fin q) :
    Potts.pottsProb G q beta J (fun x => e (sigma x)) =
      Potts.pottsProb G q beta J sigma := by
  have hagreement : Potts.agreement G (fun x => e (sigma x)) =
      Potts.agreement G sigma := by
    unfold Potts.agreement
    apply Finset.sum_congr rfl
    intro edge _
    exact Potts.monoIndicator_relabel e sigma edge
  simp [Potts.pottsProb, Potts.pottsWeight, hagreement]


theorem pottsProbWired_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    {q : Nat} [NeZero q] (b : Fin q) (e : Fin q ≃ Fin q)
    (he : e b = b) (beta J : Real) (sigma : V -> Fin q) :
    pottsProbWired G bdry q b beta J (fun x => e (sigma x)) =
      pottsProbWired G bdry q b beta J sigma := by
  have hboundary : BoundaryFixed bdry b (fun x => e (sigma x)) ↔
      BoundaryFixed bdry b sigma := by
    constructor
    · intro h x hx
      apply e.injective
      calc
        e (sigma x) = b := h x hx
        _ = e b := he.symm
    · intro h x hx
      change e (sigma x) = b
      rw [h x hx, he]
  have hagreement : Potts.agreement G (fun x => e (sigma x)) =
      Potts.agreement G sigma := by
    unfold Potts.agreement
    apply Finset.sum_congr rfl
    intro edge _
    exact Potts.monoIndicator_relabel e sigma edge
  unfold pottsProbWired pottsWeightWired
  rw [if_congr hboundary rfl rfl]
  simp [Potts.pottsWeight, hagreement]


end
end StatMech.FK

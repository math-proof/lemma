/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangBoxPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLogDerivativeBound.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangBoxPressure.Part2
open scoped BigOperators
open Finset Filter Topology Set SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

theorem isingBoxPressure_sub_reference_le
    (d m n : ℕ) (beta h : ℝ) :
    |isingBoxPressureSeq d beta h n - isingBoxPressureSeq d beta h m| ≤
      isingBoxCauchyBound d m beta h n := by
  let r := ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
    (Fintype.card (boxVerts d n) : ℝ)
  have hvh := isingBoxPressure_vanHove_abs_le d m n beta h
  change |isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m| ≤
    (Real.log 2 + |beta| * |h|) * (1 - r) +
      |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) at hvh
  calc
    |isingBoxPressureSeq d beta h n - isingBoxPressureSeq d beta h m| =
        |(isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m) +
          (r - 1) * isingBoxPressureSeq d beta h m| := by congr 1 <;> ring
    _ ≤ |isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m| +
        |r - 1| * |isingBoxPressureSeq d beta h m| := by
          simpa [abs_mul] using abs_add_le
            (isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m)
            ((r - 1) * isingBoxPressureSeq d beta h m)
    _ ≤ (Real.log 2 + |beta| * |h|) * (1 - r) +
        |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
            (Fintype.card (boxVerts d n) : ℝ)) +
          |r - 1| * |isingBoxPressureSeq d beta h m| := by
            exact add_le_add hvh (le_refl _)
    _ = isingBoxCauchyBound d m beta h n := by
      simp only [isingBoxCauchyBound, r]
      rw [abs_sub_comm]

theorem isingBoxCauchyBound_tendsto
    (d m : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto (isingBoxCauchyBound d m beta h) atTop
      (nhds (|beta| * ((d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ)))) := by
  let r : ℕ → ℝ := fun n =>
    ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
      (Fintype.card (boxVerts d n) : ℝ)
  have hr : Tendsto r atTop (nhds 1) := isingBox_vertexBulkFraction_tendsto d m
  have hfirst : Tendsto (fun n =>
      (Real.log 2 + |beta| * |h|) * (1 - r n)) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hr) using 1 <;> ring
  have hedge := (tendsto_const_nhds (x := |beta|)).mul
    (isingBox_edgeDeficitDensity_tendsto d m hd)
  have hlast : Tendsto (fun n => |1 - r n| * |isingBoxPressureSeq d beta h m|)
      atTop (nhds 0) := by
    have habs : Tendsto (fun n => |1 - r n|) atTop (nhds 0) := by
      convert (tendsto_const_nhds.sub hr).abs using 1 <;> simp
    convert habs.mul_const |isingBoxPressureSeq d beta h m| using 1 <;> ring
  have hall := (hfirst.add hedge).add hlast
  simpa only [isingBoxCauchyBound, r, zero_add, add_zero] using hall


theorem isingBoxPressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure) := by
  have hsurface : Tendsto (fun m : ℕ =>
      |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1))) atTop (nhds 0) :=
    by simpa using
      (tendsto_const_nhds (x := |beta|)).mul (isingBox_edgeSurface_tendsto_zero d)
  have hcauchy : CauchySeq (isingBoxPressureSeq d beta h) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.mp hsurface) (epsilon / 4) (by positivity)
    have hmm := hm m le_rfl
    have hsurf_nonneg : 0 ≤ |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsurf_nonneg] at hmm
    have hboundlim := isingBoxCauchyBound_tendsto d m hd beta h
    rw [isingBox_edgeSurface_eq d m hd] at hboundlim
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hboundlim) (epsilon / 4) (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    have hBa := hN a ha
    have hBb := hN b hb
    rw [Real.dist_eq] at hBa hBb ⊢
    have hBa' : isingBoxCauchyBound d m beta h a < epsilon / 2 := by
      have := le_abs_self (isingBoxCauchyBound d m beta h a -
        |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)))
      linarith
    have hBb' : isingBoxCauchyBound d m beta h b < epsilon / 2 := by
      have := le_abs_self (isingBoxCauchyBound d m beta h b -
        |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)))
      linarith
    calc
      |isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h b| =
          |(isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h m) -
            (isingBoxPressureSeq d beta h b - isingBoxPressureSeq d beta h m)| := by
              congr 1 <;> ring
      _ ≤ |isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h m| +
          |isingBoxPressureSeq d beta h b - isingBoxPressureSeq d beta h m| :=
            abs_sub _ _
      _ ≤ isingBoxCauchyBound d m beta h a + isingBoxCauchyBound d m beta h b :=
        add_le_add (isingBoxPressure_sub_reference_le d m a beta h)
          (isingBoxPressure_sub_reference_le d m b beta h)
      _ < epsilon / 2 + epsilon / 2 := add_lt_add hBa' hBb'
      _ = epsilon := by ring
  exact cauchySeq_tendsto_of_complete hcauchy


theorem isingZ_zeroField_eq_exp_mul_fkZEdge
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (beta : ℝ) :
    isingZ G beta 0 = Real.exp (beta * G.edgeFinset.card) *
      ecz_fkZEdge G (1 - Real.exp (-2 * beta)) 2 := by
  let p : ℝ := 1 - Real.exp (-2 * beta)
  have hES : fkZ G p 2 =
      esFirstConst G (2 * beta) 1 * Potts.pottsZ G 2 (2 * beta) 1 := by
    calc
      fkZ G p 2 = esZ G 2 p := (esZ_eq_fkZ G 2 p).symm
      _ = esFirstConst G (2 * beta) 1 * Potts.pottsZ G 2 (2 * beta) 1 := by
        simpa [p] using esZ_eq_pottsZ G 2 (2 * beta) 1
  rw [ecz_factorization, esFirstConst, ecz_NE_eq] at hES
  have htwo : (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hedge : ecz_fkZEdge G p 2 =
      Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card *
        Potts.pottsZ G 2 (2 * beta) 1 := by
    apply mul_left_cancel₀ htwo
    calc
      (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) * ecz_fkZEdge G p 2 =
          ((2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) *
            Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card) *
              Potts.pottsZ G 2 (2 * beta) 1 := hES
      _ = (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) *
          (Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card *
            Potts.pottsZ G 2 (2 * beta) 1) := by ring
  have hIsing := IsingFK.isingZ_eq G beta (2 * beta) 1 (by ring)
  rw [hIsing, hedge]
  rw [← Real.exp_nat_mul]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring


theorem isingBoxLogZ_zeroField_eq_fk (d n : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    isingBoxLogZ d beta 0 n =
      beta * ((boxGraph d n).edgeFinset.card : ℝ) -
        ecz_u d (fsc_logit (1 - Real.exp (-2 * beta))) n := by
  let p : ℝ := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  rw [isingBoxLogZ, isingZ_zeroField_eq_exp_mul_fkZEdge]
  rw [Real.log_mul (Real.exp_ne_zero _)
    (ecz_fkZEdge_ne_zero (boxGraph d n) hp hp1 (by norm_num)), Real.log_exp]
  unfold ecz_u
  rw [fsc_logistic_logit hp hp1]
  change beta * ((boxGraph d n).edgeFinset.card : ℝ) +
      Real.log (ecz_fkZEdge (boxGraph d n) p 2) =
    beta * ((boxGraph d n).edgeFinset.card : ℝ) -
      -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
  ring


theorem sctBoxGraph_pressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (isingZ (sctBoxGraph d n) beta h) /
          (Fintype.card (sctBox d n) : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := isingBoxPressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  unfold isingBoxPressureSeq isingBoxLogZ
  let phi : boxGraph d n ≃g sctBoxGraph d n :=
    { toEquiv := Equiv.refl (boxVerts d n)
      map_rel_iff' := by
        intro x y
        change (hypercubicLattice d).Adj (x : Site d) (y : Site d) ↔
          (hypercubicLattice d).Adj (x : Site d) (y : Site d)
        rfl }
  have hZ : isingZ (boxGraph d n) beta h = isingZ (sctBoxGraph d n) beta h :=
    isingZ_relabel _ _ phi.toEquiv (fun x y => phi.map_rel_iff.symm) beta h
  rw [hZ]


theorem freeBox_fvZ_pressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) /
          ((boxFinset d n).card : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := sctBoxGraph_pressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  rw [sct_fvZ_eq_isingZ, psv_volume_card, ecz_boxVerts_card]


theorem leeYangComplexFieldPartition_real_pressure_tendsto
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (leeYangComplexFieldPartition (boxGraph d n) beta (h : ℂ)).re /
          (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := isingBoxPressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  simp only [isingBoxPressureSeq, isingBoxLogZ,
    leeYangComplexFieldPartition_ofReal, Complex.ofReal_re]


theorem leeYangBox_pressure_and_logDerivative_analytic
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) (hbeta : 0 ≤ beta) (h : ℝ) :
    (∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure)) ∧
      ∀ n, AnalyticOnNhd ℂ
        (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        {z : ℂ | z.re ≠ 0} := by
  exact ⟨isingBoxPressure_tendsto d hd beta h,
    fun n => leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
      (boxGraph d n) hbeta⟩

end StatMech.FrontierA

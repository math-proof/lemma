/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralShiftDecay.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Def.StatisticalMechanics.Code.FK.IntegralDecayClose.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


@[simp] theorem idc_coordBcf_apply (e : Sym2 (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    idc_coordBcf e ω = if ω e then (1 : ℝ) else 0 := rfl


theorem idc_openEdgeEvent_measurable (e : Sym2 (Site d)) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
  have hpre : {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} = (fun ω => ω e) ⁻¹' {true} := by
    ext ω; simp
  rw [hpre]
  exact (measurable_pi_apply e) (measurableSet_singleton true)


theorem idc_integral_coordBcf (e : Sym2 (Site d)) (μ : Measure (ConfigSpace (Sym2 (Site d))))
    [IsFiniteMeasure μ] :
    (∫ ω, idc_coordBcf e ω ∂μ) = μ.real {ω | ω e = true} := by
  have heq : (fun ω => idc_coordBcf e ω)
      = Set.indicator {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [idc_coordBcf_apply, Set.indicator]
    by_cases h : ω e <;> simp [h, Set.mem_setOf_eq]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (idc_openEdgeEvent_measurable e)]
  simp


theorem idc_openEdge_eq_boxRestrict (N : ℕ) (eb : Sym2 (boxVerts d N)) :
    {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeIncl d N eb) = true}
      = boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, boxEdgeOpenEvent, boxRestrict]


theorem idc_integral_coordBcf_wired (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∫ ω, idc_coordBcf (edgeIncl d N eb) ω
        ∂((wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : ProbabilityMeasure _) : Measure _))
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb) := by
  rw [idc_integral_coordBcf, idc_openEdge_eq_boxRestrict,
    dfi_wired_finite_mass_eq_edgeMarg N m hNm eb hp hp1]


theorem idc_integral_coordBcf_free (N m : ℕ) (hNm : N ≤ m) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∫ ω, idc_coordBcf (edgeIncl d N eb) ω
        ∂((freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : ProbabilityMeasure _) : Measure _))
      = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) := by
  rw [idc_integral_coordBcf, idc_openEdge_eq_boxRestrict,
    dfi_free_finite_mass_eq_edgeMarg N m hNm eb hp hp1]


theorem idc_coordBcf_comp_shift (e : Sym2 (Site d)) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) :
    idc_coordBcf e (shift g ω) = idc_coordBcf (g⁻¹ • e) ω := rfl


theorem idc_decayFun_coord (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) (n : ℕ) :
    isd_decayFun μ g (idc_coordBcf e) n
      = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω e = true})
        - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (g⁻¹ • e) = true}) := by
  unfold isd_decayFun
  rw [idc_integral_coordBcf e]
  congr 1
  rw [show (fun ω => idc_coordBcf e (shift g ω)) = (fun ω => idc_coordBcf (g⁻¹ • e) ω) from
    funext (fun ω => idc_coordBcf_comp_shift e g ω)]
  rw [idc_integral_coordBcf (g⁻¹ • e)]


theorem idc_wired_coord_decay_of_density_eq (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    (g : Multiplicative (Site d)) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hshift : g⁻¹ • (edgeIncl d N eb) = edgeIncl d N eb')
    (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p) :
    Tendsto (isd_decayFun (fun m => wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2))
        g (idc_coordBcf (edgeIncl d N eb))) atTop (𝓝 0) := by
  
  have h1 : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb) = true})
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) :=
    wiredEdgeDensity_q2_tendsto d N eb hp hp1
  
  have h2 : Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb') = true})
      atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb') p)) :=
    wiredEdgeDensity_q2_tendsto d N eb' hp hp1
  
  have hdecayeq : isd_decayFun (fun m => wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2))
        g (idc_coordBcf (edgeIncl d N eb))
      = fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb) = true}
        - (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (edgeIncl d N eb') = true} := by
    funext m
    rw [idc_decayFun_coord]
    rw [hshift]
  
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this


end FK
end StatMech

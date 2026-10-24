import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.IntegralDecayClose
open MeasureTheory Filter Topology BoundedContinuousFunction StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[idc_coordCM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_coordCM_apply_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  idc_coordCM e ω = if ω e then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.FK.idc_coordCM_apply e ω

/--
[idc_coordBcf_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_coordBcf_apply_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  idc_coordBcf e ω = if ω e then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.FK.idc_coordBcf_apply e ω

/--
[idc_openEdgeEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_openEdgeEvent_measurable_eq
  {d : ℕ}
  {e : Sym2 (Site d)} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | ω e = true} := by
-- proof
  apply StatMech.FK.idc_openEdgeEvent_measurable e

/--
[idc_integral_coordBcf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_integral_coordBcf_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ] :
-- imply
  (∫ ω, idc_coordBcf e ω ∂μ) = μ.real {ω | ω e = true} := by
-- proof
  apply StatMech.FK.idc_integral_coordBcf e μ

/--
[idc_openEdge_eq_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_openEdge_eq_boxRestrict_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  {ω : ConfigSpace (Sym2 (Site d)) | ω (edgeIncl d N eb) = true} = boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb) := by
-- proof
  apply StatMech.FK.idc_openEdge_eq_boxRestrict N eb

/--
[idc_integral_coordBcf_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_integral_coordBcf_wired_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∫ ω, idc_coordBcf (edgeIncl d N eb) ω ∂((wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : ProbabilityMeasure _) : Measure _)) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb) := by
-- proof
  apply StatMech.FK.idc_integral_coordBcf_wired N m hNm eb hp hp1

/--
[idc_integral_coordBcf_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_integral_coordBcf_free_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∫ ω, idc_coordBcf (edgeIncl d N eb) ω ∂((freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : ProbabilityMeasure _) : Measure _)) = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) := by
-- proof
  apply StatMech.FK.idc_integral_coordBcf_free N m hNm eb hp hp1

/--
[idc_coordBcf_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_coordBcf_comp_shift_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  idc_coordBcf e (shift g ω) = idc_coordBcf (g⁻¹ • e) ω := by
-- proof
  apply StatMech.FK.idc_coordBcf_comp_shift e g ω

/--
[idc_decayFun_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_decayFun_coord_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)}
  {n : ℕ} :
-- imply
  isd_decayFun μ g (idc_coordBcf e) n = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω e = true}) - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real {ω | ω (g⁻¹ • e) = true}) := by
-- proof
  apply StatMech.FK.idc_decayFun_coord μ g e n

/--
[idc_wired_coord_decay_of_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wired_coord_decay_of_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {g : Multiplicative (Site d)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hshift : g⁻¹ • (edgeIncl d N eb) = edgeIncl d N eb')
  (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p) :
-- imply
  Tendsto (isd_decayFun (fun m => wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)) g (idc_coordBcf (edgeIncl d N eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.idc_wired_coord_decay_of_density_eq N eb eb' g hp hp1 hshift hdens

/--
[idc_cylinderAlg_separatesPoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_cylinderAlg_separatesPoints_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  (idc_cylinderAlg d).SeparatesPoints := by
-- proof
  apply StatMech.FK.idc_cylinderAlg_separatesPoints d

/--
[idc_cylinderBcfSet_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_cylinderBcfSet_dense_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Dense (idc_cylinderBcfSet d) := by
-- proof
  apply StatMech.FK.idc_cylinderBcfSet_dense d

/--
[idc_wiredDenseDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wiredDenseDecay_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
-- imply
  isd_wiredDenseDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.idc_wiredDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl

/--
[idc_freeDenseDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_freeDenseDecay_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
-- imply
  isd_freeDenseDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.idc_freeDenseDecay_of_cylinderDecay hp hp1 hq g φ hcyl

/--
[idc_wiredIntegralShiftDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wiredIntegralShiftDecay_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : idc_wiredCylinderDecay hp hp1 hq g φ) :
-- imply
  ivt_wiredIntegralShiftDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.idc_wiredIntegralShiftDecay_of_cylinderDecay hp hp1 hq g φ hcyl

/--
[idc_freeIntegralShiftDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_freeIntegralShiftDecay_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : idc_freeCylinderDecay hp hp1 hq g φ) :
-- imply
  ivt_freeIntegralShiftDecay hp hp1 hq g φ := by
-- proof
  apply StatMech.FK.idc_freeIntegralShiftDecay_of_cylinderDecay hp hp1 hq g φ hcyl

/--
[idc_wiredCylinderDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wiredCylinderDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  idc_wiredCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.idc_wiredCylinderDecay_one hp hp1 hq φ

/--
[idc_freeCylinderDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_freeCylinderDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  idc_freeCylinderDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.idc_freeCylinderDecay_one hp hp1 hq φ

/--
[idc_wiredIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wiredIntegralShiftDecay_one_eq
  {d : ℕ}
  {p q : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ivt_wiredIntegralShiftDecay hp hp1 hq (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.idc_wiredIntegralShiftDecay_one hp hp1 hq φ

/--
[idc_wiredIV_isTranslationInvariant_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_wiredIV_isTranslationInvariant_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 hq) (wiredInfiniteVolume d hp hp1 hq) → idc_wiredCylinderDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.idc_wiredIV_isTranslationInvariant_of_cylinderDecay hp hp1 hq hcyl

/--
[idc_freeIV_isTranslationInvariant_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralDecayClose.lean)
-/
@[path]
private lemma idc_freeIV_isTranslationInvariant_of_cylinderDecay_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 hq) (freeInfiniteVolume d hp hp1 hq) → idc_freeCylinderDecay hp hp1 hq g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.idc_freeIV_isTranslationInvariant_of_cylinderDecay hp hp1 hq hcyl


-- created on 2026-10-23

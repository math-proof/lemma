import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[cdc_eventMassProb_reCfgIso_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_eventMassProb_reCfgIso_inv_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {σ : V ≃ W}
  {μV : ConfigSpace (Sym2 V) → ℝ}
  {μW : ConfigSpace (Sym2 W) → ℝ}
  {S : Set (ConfigSpace (Sym2 V))}
-- given
  (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) :
-- imply
  ∑ ω : ConfigSpace (Sym2 W), (reCfgIso σ ⁻¹' S).indicator (fun _ => (1:ℝ)) ω * μW ω = ∑ η : ConfigSpace (Sym2 V), S.indicator (fun _ => (1:ℝ)) η * μV η := by
-- proof
  apply StatMech.FK.cdc_eventMassProb_reCfgIso_inv σ μV μW hμ S

/--
[cdc_prod_coordCM_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_prod_coordCM_eq_indicator_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (∏ e ∈ s, idc_coordCM e ω) = (cdc_multiOpenEvent s).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.FK.cdc_prod_coordCM_eq_indicator s ω

/--
[cdc_multiOpenEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_multiOpenEvent_isIncreasing_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))} :
-- imply
  IsIncreasing (cdc_multiOpenEvent s) := by
-- proof
  apply StatMech.FK.cdc_multiOpenEvent_isIncreasing s

/--
[cdc_multiOpenEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_multiOpenEvent_measurable_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))} :
-- imply
  MeasurableSet (cdc_multiOpenEvent s) := by
-- proof
  apply StatMech.FK.cdc_multiOpenEvent_measurable s

/--
[cdc_monomialCM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialCM_apply_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cdc_monomialCM s ω = ∏ e ∈ s, idc_coordCM e ω := by
-- proof
  apply StatMech.FK.cdc_monomialCM_apply s ω

/--
[cdc_monomialBcf_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialBcf_apply_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cdc_monomialBcf s ω = ∏ e ∈ s, idc_coordCM e ω := by
-- proof
  apply StatMech.FK.cdc_monomialBcf_apply s ω

/--
[cdc_integral_monomialBcf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_integral_monomialBcf_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ] :
-- imply
  (∫ ω, cdc_monomialBcf s ω ∂μ) = μ.real (cdc_multiOpenEvent s) := by
-- proof
  apply StatMech.FK.cdc_integral_monomialBcf s μ

/--
[cdc_monomialBcf_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialBcf_comp_shift_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cdc_monomialBcf s (shift g ω) = (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.FK.cdc_monomialBcf_comp_shift s g ω

/--
[cdc_decayFun_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_monomial_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {s : Finset (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  isd_decayFun μ g (cdc_monomialBcf s) n = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s)) - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))) := by
-- proof
  apply StatMech.FK.cdc_decayFun_monomial μ g s n

/--
[cdc_boxMultiOpenEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_boxMultiOpenEvent_isIncreasing_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))} :
-- imply
  IsIncreasing (cdc_boxMultiOpenEvent N t) := by
-- proof
  apply StatMech.FK.cdc_boxMultiOpenEvent_isIncreasing N t

/--
[cdc_multiOpenEvent_image_eq_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_multiOpenEvent_image_eq_boxRestrict_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))} :
-- imply
  cdc_multiOpenEvent (t.image (edgeIncl d N)) = boxRestrict d N ⁻¹' (cdc_boxMultiOpenEvent N t) := by
-- proof
  apply StatMech.FK.cdc_multiOpenEvent_image_eq_boxRestrict N t

/--
[cdc_wired_multiOpenEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_wired_multiOpenEvent_tendsto_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop (𝓝 ((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.cdc_wired_multiOpenEvent_tendsto N t hp hp1

/--
[cdc_free_multiOpenEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_free_multiOpenEvent_tendsto_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N)))) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (t.image (edgeIncl d N))))) := by
-- proof
  apply StatMech.FK.cdc_free_multiOpenEvent_tendsto N t hp hp1

/--
[cdc_edge_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_edge_mem_range_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {x y : Site d}
  {N : ℕ}
-- given
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  s(x, y) ∈ Set.range (edgeIncl d N) := by
-- proof
  apply StatMech.FK.cdc_edge_mem_range x y hx hy

/--
[cdc_finset_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_finset_in_box_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s : Finset (Sym2 (Site d))} :
-- imply
  ∃ (N : ℕ) (t : Finset (Sym2 (boxVerts d N))), s = t.image (edgeIncl d N) := by
-- proof
  apply StatMech.FK.cdc_finset_in_box s

/--
[cdc_decayFun_monomial_wired_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_monomial_wired_tendsto_zero_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
  {s : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
-- imply
  Tendsto (isd_decayFun (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g (cdc_monomialBcf s)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.cdc_decayFun_monomial_wired_tendsto_zero hp hp1 g φ hφ hhom s

/--
[cdc_decayFun_monomial_free_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_monomial_free_tendsto_zero_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
  {s : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
-- imply
  Tendsto (isd_decayFun (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) g (cdc_monomialBcf s)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.cdc_decayFun_monomial_free_tendsto_zero hp hp1 g φ hφ hhom s

/--
[cdc_monomialCM_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialCM_empty_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W] :
-- imply
  cdc_monomialCM (∅ : Finset (Sym2 (Site d))) = 1 := by
-- proof
  apply StatMech.FK.cdc_monomialCM_empty

/--
[cdc_monomialCM_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialCM_singleton_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {e : Sym2 (Site d)} :
-- imply
  cdc_monomialCM ({e} : Finset (Sym2 (Site d))) = idc_coordCM e := by
-- proof
  apply StatMech.FK.cdc_monomialCM_singleton e

/--
[cdc_monomialCM_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_monomialCM_mul_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {s₁ s₂ : Finset (Sym2 (Site d))} :
-- imply
  cdc_monomialCM s₁ * cdc_monomialCM s₂ = cdc_monomialCM (s₁ ∪ s₂) := by
-- proof
  apply StatMech.FK.cdc_monomialCM_mul s₁ s₂

/--
[cdc_closure_isMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_closure_isMonomial_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {h : C(ConfigSpace (Sym2 (Site d)), ℝ)}
-- given
  (hh : h ∈ Submonoid.closure (Set.range (idc_coordCM (d := d)))) :
-- imply
  ∃ s : Finset (Sym2 (Site d)), h = cdc_monomialCM s := by
-- proof
  apply StatMech.FK.cdc_closure_isMonomial hh

/--
[cdc_decayFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_add_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {f f' : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  isd_decayFun μ g (f + f') n = isd_decayFun μ g f n + isd_decayFun μ g f' n := by
-- proof
  apply StatMech.FK.cdc_decayFun_add μ g f f' n

/--
[cdc_decayFun_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_smul_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {c : ℝ}
  {f : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  isd_decayFun μ g (c • f) n = c * isd_decayFun μ g f n := by
-- proof
  apply StatMech.FK.cdc_decayFun_smul μ g c f n

/--
[cdc_decayFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_decayFun_zero_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {g : Multiplicative (Site d)}
  {n : ℕ} :
-- imply
  isd_decayFun μ g (0 : ConfigSpace (Sym2 (Site d)) →ᵇ ℝ) n = 0 := by
-- proof
  apply StatMech.FK.cdc_decayFun_zero μ g n

/--
[cdc_cylinderAlg_le_wiredDecaySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_cylinderAlg_le_wiredDecaySet_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
-- imply
  Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_wiredDecaySet hp hp1 g φ := by
-- proof
  apply StatMech.FK.cdc_cylinderAlg_le_wiredDecaySet hp hp1 g φ hφ hhom

/--
[cdc_cylinderAlg_le_freeDecaySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_cylinderAlg_le_freeDecaySet_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
-- imply
  Subalgebra.toSubmodule (idc_cylinderAlg d) ≤ cdc_freeDecaySet hp hp1 g φ := by
-- proof
  apply StatMech.FK.cdc_cylinderAlg_le_freeDecaySet hp hp1 g φ hφ hhom

/--
[cdc_wiredCylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_wiredCylinderDecay_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_wiredMultiHomogeneous hp hp1 g) :
-- imply
  idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
-- proof
  apply StatMech.FK.cdc_wiredCylinderDecay hp hp1 g φ hφ hhom

/--
[cdc_freeCylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_freeCylinderDecay_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ)
  (hhom : cdc_freeMultiHomogeneous hp hp1 g) :
-- imply
  idc_freeCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) g φ := by
-- proof
  apply StatMech.FK.cdc_freeCylinderDecay hp hp1 g φ hφ hhom

/--
[cdc_wiredMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_wiredMultiHomogeneous_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_wiredMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.cdc_wiredMultiHomogeneous_one hp hp1

/--
[cdc_freeMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_freeMultiHomogeneous_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.FK.cdc_freeMultiHomogeneous_one hp hp1

/--
[cdc_wiredCylinderDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_wiredCylinderDecay_one_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hφ : StrictMono φ) :
-- imply
  idc_wiredCylinderDecay hp hp1 (by norm_num : (0:ℝ) < 2) (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.FK.cdc_wiredCylinderDecay_one hp hp1 φ hφ

/--
[cdc_wiredIV_isTranslationInvariant_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_wiredIV_isTranslationInvariant_of_homogeneous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => wiredFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) → cdc_wiredMultiHomogeneous hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.cdc_wiredIV_isTranslationInvariant_of_homogeneous hp hp1 hhom

/--
[cdc_freeIV_isTranslationInvariant_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean)
-/
@[path]
private lemma cdc_freeIV_isTranslationInvariant_of_homogeneous_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hhom : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => freeFiniteMeasure d (φ n) hp hp1 (by norm_num : (0:ℝ) < 2)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2)) → cdc_freeMultiHomogeneous hp hp1 g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.cdc_freeIV_isTranslationInvariant_of_homogeneous hp hp1 hhom


-- created on 2026-10-23

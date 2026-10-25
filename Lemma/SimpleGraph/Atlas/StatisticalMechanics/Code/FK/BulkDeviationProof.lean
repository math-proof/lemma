import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[bdp_boundaryCliqueGraph_noBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_boundaryCliqueGraph_noBdry_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout} :
-- imply
  StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout)) = (⊥ : SimpleGraph Vout) := by
-- proof
  apply StatMech.FK.bdp_boundaryCliqueGraph_noBdry

/--
[bdp_numClustersBC_noBdry_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_numClustersBC_noBdry_eq_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {ω : ConfigSpace (Sym2 Vout)} :
-- imply
  numClustersBC Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) ω = numClusters Gout ω := by
-- proof
  apply StatMech.FK.bdp_numClustersBC_noBdry_eq ω

/--
[bdp_bcWeight_noBdry_eq_fkWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_bcWeight_noBdry_eq_fkWeight_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 Vout)} :
-- imply
  bcWeight Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q ω = fkWeight Gout p q ω := by
-- proof
  apply StatMech.FK.bdp_bcWeight_noBdry_eq_fkWeight ω

/--
[bdp_bcProb_noBdry_eq_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_bcProb_noBdry_eq_fkProb_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {ρ : ConfigSpace (Sym2 Vout)} :
-- imply
  bcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q ρ = fkProb Gout p q ρ := by
-- proof
  apply StatMech.FK.bdp_bcProb_noBdry_eq_fkProb ρ

/--
[bdp_condBcProb_innerRestrict_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_condBcProb_innerRestrict_ge_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω) ≤ ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph (bdp_noBdry (Vout := Vout))) p q (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ := by
-- proof
  apply StatMech.FK.bdp_condBcProb_innerRestrict_ge hι hadjm hp hp1 hq ψ hA

/--
[bdp_free_inner_dominated_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_free_inner_dominated_fkProb_eq
  {d : ℕ}
  [Fintype Vin]
  [DecidableEq Vin]
  [Fintype Vout]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ω, A.indicator (fun _ => (1:ℝ)) ω * fkProb Gin p q ω) ≤ ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * fkProb Gout p q ρ := by
-- proof
  apply StatMech.FK.bdp_free_inner_dominated_fkProb hι hadjm hp hp1 hq hA

/--
[bdp_latticeFree_multiMass_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_latticeFree_multiMass_dominated_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype Sin]
  [Fintype Sout]
  {p q : ℝ}
-- given
  (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
  (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
  (hιinj : Function.Injective ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (t : Finset (Sym2 {y : Site d // y ∈ Sin})) :
-- imply
  med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q) t ≤ med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q) (t.image (ocd_innerEdge ιV)) := by
-- proof
  apply StatMech.FK.bdp_latticeFree_multiMass_dominated ιV hιval hιinj hp hp1 hq t

/--
[bdp_centred_med_eq_measure_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_centred_med_eq_measure_free_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {n : ℕ}
  {tb : Finset (Sym2 (boxVerts d n))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  med_multiMassProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p 2) tb = (freeFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent (tb.image (edgeIncl d n))) := by
-- proof
  apply StatMech.FK.bdp_centred_med_eq_measure_free n tb hp hp1

/--
[bdp_freeSqueeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeSqueeze_upper_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m) :
-- imply
  lmc_transBoxMassFree v N t p m hNm ≤ (freeFiniteMeasure d (m + flc_vrad v + 1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) := by
-- proof
  apply StatMech.FK.bdp_freeSqueeze_upper v N t hp hp1 m hNm

/--
[bdp_freeSqueeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeSqueeze_lower_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
  {m a : ℕ}
  {tb_a : Finset (Sym2 (boxVerts d a))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hNm : N ≤ m)
  (hcond : a + flc_vrad v + 1 ≤ m)
  (htb : tb_a.image (edgeIncl d a) = (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e)) :
-- imply
  (freeFiniteMeasure d a hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))) ≤ lmc_transBoxMassFree v N t p m hNm := by
-- proof
  apply StatMech.FK.bdp_freeSqueeze_lower v N t hp hp1 m a hNm hcond tb_a htb

/--
[bdp_transBoxMassFree_tendsto_translated_iv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_transBoxMassFree_tendsto_translated_iv_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {v : Site d}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun m' : ℕ => lmc_transBoxMassFree v N t p (N + m') (Nat.le_add_right N m')) atTop (𝓝 ((freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent ((t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e))))) := by
-- proof
  apply StatMech.FK.bdp_transBoxMassFree_tendsto_translated_iv v N t hp hp1

/--
[bdp_freePlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freePlacement_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  lmc_freePlacement hp hp1 g := by
-- proof
  apply StatMech.FK.bdp_freePlacement hp hp1 g

/--
[bdp_freePlacement_forall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freePlacement_forall_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ∀ g : Multiplicative (Site d), lmc_freePlacement hp hp1 g := by
-- proof
  apply StatMech.FK.bdp_freePlacement_forall hp hp1

/--
[bdp_freeMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeMultiHomogeneous_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
  {g : Multiplicative (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  cdc_freeMultiHomogeneous hp hp1 g := by
-- proof
  apply StatMech.FK.bdp_freeMultiHomogeneous hp hp1 g

/--
[bdp_freeIV_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeIV_isTranslationInvariant_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.bdp_freeIV_isTranslationInvariant hp hp1

/--
[bdp_edgeMargProb_eq_med_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_edgeMargProb_eq_med_singleton_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V} :
-- imply
  edgeMargProb μ e = med_multiMassProb μ {e} := by
-- proof
  apply StatMech.FK.bdp_edgeMargProb_eq_med_singleton μ e

/--
[bdp_measurableSet_fkEdgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_measurableSet_fkEdgeOpenEvent_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {e : E} :
-- imply
  MeasurableSet (fkEdgeOpenEvent e) := by
-- proof
  apply StatMech.FK.bdp_measurableSet_fkEdgeOpenEvent e

/--
[bdp_shift_preimage_fkEdgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_shift_preimage_fkEdgeOpenEvent_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  (ConfigSpace.shift g : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' (fkEdgeOpenEvent e) = fkEdgeOpenEvent (g⁻¹ • e) := by
-- proof
  apply StatMech.FK.bdp_shift_preimage_fkEdgeOpenEvent g e

/--
[bdp_freeEdgeDensity_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeEdgeDensity_translation_inv_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 e p = freeEdgeDensity d 2 (g⁻¹ • e) p := by
-- proof
  apply StatMech.FK.bdp_freeEdgeDensity_translation_inv hp hp1 g e

/--
[bdp_wiredEdgeDensity_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_wiredEdgeDensity_translation_inv_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {p : ℝ}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 e p = wiredEdgeDensity d 2 (g⁻¹ • e) p := by
-- proof
  apply StatMech.FK.bdp_wiredEdgeDensity_translation_inv hp hp1 g e

/--
[bdp_free_per_edge_box_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_free_per_edge_box_mono_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {a n : ℕ}
  {eb : Sym2 (boxVerts d a)}
  {p : ℝ}
-- given
  (hle : a ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (fkProb (boxGraph d a) p 2) eb ≤ edgeMargProb (fkProb (boxGraph d n) p 2) (innerEdgeLE d hle eb) := by
-- proof
  apply StatMech.FK.bdp_free_per_edge_box_mono a n hle eb hp hp1

/--
[bdp_innerEdgeLE_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_innerEdgeLE_refl_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)} :
-- imply
  innerEdgeLE d (le_refl n) e = e := by
-- proof
  apply StatMech.FK.bdp_innerEdgeLE_refl n e

/--
[bdp_free_per_edge_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_free_per_edge_upper_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (fkProb (boxGraph d n) p 2) e ≤ freeEdgeDensity d 2 (edgeIncl d n e) p := by
-- proof
  apply StatMech.FK.bdp_free_per_edge_upper n e hp hp1

/--
[bdp_wired_per_edge_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_wired_per_edge_lower_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d n e) p ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
-- proof
  apply StatMech.FK.bdp_wired_per_edge_lower n e hp hp1

/--
[bdp_freeUniformBulkDeviation_of_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_freeUniformBulkDeviation_of_sandwich_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {N : ℕ}
-- given
  (hsand : bdp_FreeOffCentreSandwich (d := d) N) :
-- imply
  ubd_FreeUniformBulkDeviation (d := d) N := by
-- proof
  apply StatMech.FK.bdp_freeUniformBulkDeviation_of_sandwich N hsand

/--
[bdp_wiredUniformBulkDeviation_of_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_wiredUniformBulkDeviation_of_sandwich_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {N : ℕ}
-- given
  (hsand : bdp_WiredOffCentreSandwich (d := d) N) :
-- imply
  ubd_WiredUniformBulkDeviation (d := d) N := by
-- proof
  apply StatMech.FK.bdp_wiredUniformBulkDeviation_of_sandwich N hsand

/--
[bdp_fk_uniqueness_of_offCentreSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BulkDeviationProof.lean)
-/
@[path]
private lemma bdp_fk_uniqueness_of_offCentreSandwich_eq
  {d : ℕ}
  {Sin Sout : Set (Site d)}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hfreeSand : bdp_FreeOffCentreSandwich (d := d) N)
  (hwiredSand : bdp_WiredOffCentreSandwich (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.bdp_fk_uniqueness_of_offCentreSandwich hd N eb hEbox hg hboxfree hfreeSand hwiredSand


-- created on 2026-10-23

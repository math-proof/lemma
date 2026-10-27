import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.CrossBoxGeneralKeystone.Part3
open MeasureTheory Filter Topology Set SimpleGraph StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[cbk_boxVertInclLE_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_boxVertInclLE_val_eq
  {d : ℕ}
  {N m : ℕ}
  {x : boxVerts d N}
-- given
  (h : N ≤ m) :
-- imply
  (boxVertInclLE d h x : Site d) = (x : Site d) := by
-- proof
  apply StatMech.FK.cbk_boxVertInclLE_val h x

/--
[cbk_boxVertInclLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_boxVertInclLE_injective_eq
  {d : ℕ}
  {N m : ℕ}
-- given
  (h : N ≤ m) :
-- imply
  Function.Injective (boxVertInclLE d h) := by
-- proof
  apply StatMech.FK.cbk_boxVertInclLE_injective h

/--
[cbk_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_adjMatch_eq
  {d : ℕ}
  {N m : ℕ}
-- given
  (h : N ≤ m) :
-- imply
  ocd_AdjMatch (boxGraph d N) (boxGraph d m) (boxVertInclLE d h) := by
-- proof
  apply StatMech.FK.cbk_adjMatch h

/--
[cbk_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_margin_eq
  {d : ℕ}
  {N m : ℕ}
  {x : boxVerts d N}
-- given
  (hNm : N < m) :
-- imply
  ¬ boxBoundary d m (boxVertInclLE d (le_of_lt hNm) x) := by
-- proof
  apply StatMech.FK.cbk_margin hNm x

/--
[cbk_bdryIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_bdryIn_eq
  {d : ℕ}
  {N : ℕ}
  {x : boxVerts d N}
  {z : Site d}
-- given
  (hN : 1 ≤ N)
  (hnn : NearestNeighbour d (x : Site d) z)
  (hz : z ∉ box d N) :
-- imply
  boxBoundary d N x := by
-- proof
  apply StatMech.FK.cbk_bdryIn hN x z hnn hz

/--
[cbk_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_inducedWiring_le_eq
  {d : ℕ}
  {N m : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d m))}
-- given
  (hN : 1 ≤ N)
  (hNm : N < m) :
-- imply
  ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) (boxBoundary d m) ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
-- proof
  apply StatMech.FK.cbk_inducedWiring_le hN hNm ψ

/--
[cbk_condBcProb_innerRestrict_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_condBcProb_innerRestrict_le_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d m))}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hN : 1 ≤ N)
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ ρ, (ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d m) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d m)) p q (ocd_innerEdgeFinset (boxVertInclLE d (le_of_lt hNm))) ψ ρ) ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d N) (boxBoundary d N) p q ω := by
-- proof
  apply StatMech.FK.cbk_condBcProb_innerRestrict_le hN hNm hp hp1 hq ψ hA

/--
[cbk_nearMass_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_nearMass_eq_sum_eq
  {d : ℕ}
  {N : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t.image (edgeIncl d N))) = ∑ ω, (cdc_boxMultiOpenEvent N t).indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d N) (boxBoundary d N) p 2 ω := by
-- proof
  apply StatMech.FK.cbk_nearMass_eq_sum N t hp hp1

/--
[cbk_ocd_innerEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_ocd_innerEdge_eq_eq
  {d : ℕ}
  {N m : ℕ}
-- given
  (h : N ≤ m) :
-- imply
  ocd_innerEdge (boxVertInclLE d h) = innerEdgeLE d h := by
-- proof
  apply StatMech.FK.cbk_ocd_innerEdge_eq h

/--
[cbk_innerRestrict_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_innerRestrict_preimage_eq
  {d : ℕ}
  {N m : ℕ}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (h : N ≤ m) :
-- imply
  ocd_innerRestrict (boxVertInclLE d h) ⁻¹' (cdc_boxMultiOpenEvent N t) = cdc_boxMultiOpenEvent m (t.image (innerEdgeLE d h)) := by
-- proof
  apply StatMech.FK.cbk_innerRestrict_preimage h t

/--
[cbk_boxMultiOpen_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_boxMultiOpen_increasing_eq
  {d : ℕ}
  {m : ℕ}
  {s : Finset (Sym2 (boxVerts d m))} :
-- imply
  IsIncreasing (cdc_boxMultiOpenEvent m s) := by
-- proof
  apply StatMech.FK.cbk_boxMultiOpen_increasing m s

/--
[cbk_vrad_shiftVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_vrad_shiftVec_eq
  {d : ℕ}
  {d : ℕ}
  {i₀ : Fin d}
  {N : ℕ} :
-- imply
  flc_vrad (cbk_shiftVec i₀ N) = 2 * N + 1 := by
-- proof
  apply StatMech.FK.cbk_vrad_shiftVec i₀ N

/--
[cbk_box_disjoint_transBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_box_disjoint_transBox_eq
  {d : ℕ}
  {d : ℕ}
  {i₀ : Fin d}
  {N : ℕ}
  {y : Site d}
-- given
  (hy : y ∈ box d N)
  (hyt : y ∈ fvs_transBox d N (cbk_shiftVec i₀ N)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.cbk_box_disjoint_transBox i₀ N hy hyt

/--
[cbk_edgeIncl_shiftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_edgeIncl_shiftEdge_eq
  {d : ℕ}
  {N r : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hv : flc_vrad v ≤ r) :
-- imply
  edgeIncl d (N + r) (cbk_shiftEdge v hv eb) = (Multiplicative.ofAdd v) • (edgeIncl d N eb) := by
-- proof
  apply StatMech.FK.cbk_edgeIncl_shiftEdge v hv eb

/--
[cbk_shifted_realised](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_shifted_realised_eq
  {d : ℕ}
  {N r : ℕ}
  {v : Site d}
  {t : Finset (Sym2 (boxVerts d N))}
-- given
  (hv : flc_vrad v ≤ r) :
-- imply
  (t.image (edgeIncl d N)).image (fun e => (Multiplicative.ofAdd v) • e) = (t.image (cbk_shiftEdge v hv)).image (edgeIncl d (N + r)) := by
-- proof
  apply StatMech.FK.cbk_shifted_realised v hv t

/--
[cbk_innerEdgeLE_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_innerEdgeLE_eq_eq
  {d : ℕ}
  {N r : ℕ}
-- given
  (h : N ≤ N + r) :
-- imply
  (Set.range (innerEdgeLE d h)) = Set.range (ocd_innerEdge (boxVertInclLE d h)) := by
-- proof
  apply StatMech.FK.cbk_innerEdgeLE_eq h

/--
[cbk_shiftBoxVert_not_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_shiftBoxVert_not_inner_eq
  {d : ℕ}
  {N r : ℕ}
  {i₀ : Fin d}
  {hv : flc_vrad (cbk_shiftVec i₀ N) ≤ r}
  {a : boxVerts d N} :
-- imply
  ((cbk_shiftBoxVert (cbk_shiftVec i₀ N) hv a : boxVerts d (N + r)) : Site d) ∉ box d N := by
-- proof
  apply StatMech.FK.cbk_shiftBoxVert_not_inner i₀ a

/--
[cbk_shiftEdge_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_shiftEdge_not_range_eq
  {d : ℕ}
  {N r : ℕ}
  {i₀ : Fin d}
  {hv : flc_vrad (cbk_shiftVec i₀ N) ≤ r}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  cbk_shiftEdge (cbk_shiftVec i₀ N) hv eb ∉ Set.range (innerEdgeLE d (Nat.le_add_right N r)) := by
-- proof
  apply StatMech.FK.cbk_shiftEdge_not_range i₀ eb

/--
[cbk_boxMultiOpen_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_boxMultiOpen_union_eq
  {d : ℕ}
  {m : ℕ}
  {s s' : Finset (Sym2 (boxVerts d m))} :
-- imply
  cdc_boxMultiOpenEvent m (s ∪ s') = cdc_boxMultiOpenEvent m s ∩ cdc_boxMultiOpenEvent m s' := by
-- proof
  apply StatMech.FK.cbk_boxMultiOpen_union m s s'

/--
[cbk_dependsOnOutside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_dependsOnOutside_eq
  {d : ℕ}
  {m : ℕ}
  {F : Finset (Sym2 (boxVerts d m))}
  {s : Finset (Sym2 (boxVerts d m))}
-- given
  (hsF : ∀ e ∈ s, e ∉ F) :
-- imply
  DependsOnOutside F (cdc_boxMultiOpenEvent m s) := by
-- proof
  apply StatMech.FK.cbk_dependsOnOutside F s hsF

/--
[cbk_factorise_pair_ge1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_factorise_pair_ge1_eq
  {d : ℕ}
  {d : ℕ}
  {i₀ : Fin d}
  {N : ℕ}
  {p : ℝ}
  {t_T t_T' : Finset (Sym2 (boxVerts d N))}
-- given
  (hN : 1 ≤ N)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (N + (flc_vrad (cbk_shiftVec i₀ N) + 1)) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t_T.image (edgeIncl d N)) ∩ (shift (Multiplicative.ofAdd (- cbk_shiftVec i₀ N)) : ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) ⁻¹' fmu_multiOpen (t_T'.image (edgeIncl d N))) ≤ (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t_T.image (edgeIncl d N))) * (wiredFiniteMeasure d N hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen (t_T'.image (edgeIncl d N))) := by
-- proof
  apply StatMech.FK.cbk_factorise_pair_ge1 i₀ hN hp hp1 t_T t_T'

/--
[cbk_wiredDisjointBoxFactorise_ge1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_wiredDisjointBoxFactorise_ge1_eq
  {d : ℕ}
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.cbk_wiredDisjointBoxFactorise_ge1 hd hp hp1

/--
[cbk_wiredIV_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CrossBoxGeneralKeystone.lean)
-/
@[path]
private lemma cbk_wiredIV_isErgodic_eq
  {d : ℕ}
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.cbk_wiredIV_isErgodic hd hp hp1


-- created on 2026-10-23

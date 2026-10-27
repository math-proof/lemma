import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[outProj_eq_false_of_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma outProj_eq_false_of_range_eq
  {d : ℕ}
  {n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {e : Sym2 (boxVerts d (n+1))}
-- given
  (he : e ∈ Set.range (innerEdge d n)) :
-- imply
  outProj d n ρ e = false := by
-- proof
  apply StatMech.FK.outProj_eq_false_of_range n ρ he

/--
[outProj_eq_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma outProj_eq_of_not_range_eq
  {d : ℕ}
  {n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {e : Sym2 (boxVerts d (n+1))}
-- given
  (he : e ∉ Set.range (innerEdge d n)) :
-- imply
  outProj d n ρ e = ρ e := by
-- proof
  apply StatMech.FK.outProj_eq_of_not_range n ρ he

/--
[agreesOff_outProj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma agreesOff_outProj_eq
  {d : ℕ}
  {n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  AgreesOff (innerEdgeFinset d n) (outProj d n ρ) ρ := by
-- proof
  apply StatMech.FK.agreesOff_outProj n ρ

/--
[outProj_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma outProj_idem_eq
  {d : ℕ}
  {n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  outProj d n (outProj d n ρ) = outProj d n ρ := by
-- proof
  apply StatMech.FK.outProj_idem n ρ

/--
[filter_outProj_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma filter_outProj_eq_condFibre_eq
  {d : ℕ}
  {n : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
-- given
  (hψ : outProj d n ψ = ψ) :
-- imply
  Finset.univ.filter (fun ρ => outProj d n ρ = ψ) = condFibre (innerEdgeFinset d n) ψ := by
-- proof
  apply StatMech.FK.filter_outProj_eq_condFibre n ψ hψ

/--
[condFibre_congr_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma condFibre_congr_dom_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {ψ ψ' : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ψ') :
-- imply
  condFibre F ψ = condFibre F ψ' := by
-- proof
  apply StatMech.FK.condFibre_congr_dom h

/--
[condBcProb_congr_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma condBcProb_congr_dom_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {p q : ℝ}
  {F : Finset (Sym2 V)}
  {ψ ψ' ω : ConfigSpace (Sym2 V)}
-- given
  (h : AgreesOff F ψ ψ') :
-- imply
  condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
-- proof
  apply StatMech.FK.condBcProb_congr_dom G C p q F ψ ψ' ω h

/--
[sum_fibreMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma sum_fibreMass_eq_one_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ), (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) = 1 := by
-- proof
  apply StatMech.FK.sum_fibreMass_eq_one n hp hp1 hq

/--
[wiredSucc_bcProb_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredSucc_bcProb_decompose_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ) = ∑ ψ ∈ Finset.univ.filter (fun ψ => outProj d n ψ = ψ), (∑ σ ∈ condFibre (innerEdgeFinset d n) ψ, bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q σ) * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q (innerEdgeFinset d n) ψ ρ) := by
-- proof
  apply StatMech.FK.wiredSucc_bcProb_decompose n hp hp1 hq B

/--
[condBcProb_innerRestrict_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma condBcProb_innerRestrict_le_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
  {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA₀ : IsIncreasing A₀) :
-- imply
  (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q (innerEdgeFinset d n) ψ ρ) ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_innerRestrict_le n hp hp1 hq ψ hA₀

/--
[wiredSucc_bcProb_innerEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredSucc_bcProb_innerEvent_le_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {A₀ : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA₀ : IsIncreasing A₀) :
-- imply
  (∑ ρ, (innerRestrict d n ⁻¹' A₀).indicator (fun _ => (1:ℝ)) ρ * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p q ρ) ≤ ∑ ω, A₀.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.wiredSucc_bcProb_innerEvent_le n hp hp1 hq hA₀

/--
[wiredFiniteMeasure_succ_real_innerRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_succ_real_innerRestrictEvent_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))), (innerRestrict d n ⁻¹' S).indicator (fun _ => (1:ℝ)) ρ * bcProb (boxGraph d (n+1)) (boundaryCliqueGraph (boxBoundary d (n+1))) p 2 ρ := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 S hmeas

/--
[wiredFiniteMeasure_succ_le_smallerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_succ_le_smallerBox_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) ≤ ∑ ω, S.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_succ_le_smallerBox n hp hp1 hS hmeas

/--
[isIncreasing_connToBdryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma isIncreasing_connToBdryEvent_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  IsIncreasing {ω : ConfigSpace (Sym2 (boxVerts d n)) | ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
-- proof
  apply StatMech.FK.isIncreasing_connToBdryEvent n

/--
[wiredFiniteMeasure_succ_le_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_succ_le_boxBdryConnEvent_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_succ_le_boxBdryConnEvent n hp hp1

/--
[openSub_succ_adj_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma openSub_succ_adj_inner_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : boxVerts d n} :
-- imply
  (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj (boxVertIncl d n x) (boxVertIncl d n y) ↔ (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
-- proof
  apply StatMech.FK.openSub_succ_adj_inner n ω x y

/--
[boxBoundary_of_openSub_succ_adj_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBoundary_of_openSub_succ_adj_outer_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : boxVerts d n}
  {z : boxVerts d (n+1)}
-- given
  (hn : 1 ≤ n)
  (hz : ¬ IsInnerVert d n z)
  (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Adj (boxVertIncl d n x) z) :
-- imply
  boxBoundary d n x := by
-- proof
  apply StatMech.FK.boxBoundary_of_openSub_succ_adj_outer n hn ω hz h

/--
[boxVertIncl_boxOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxVertIncl_boxOrigin_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  boxVertIncl d n (IsingFK.boxOrigin d n) = IsingFK.boxOrigin d (n+1) := by
-- proof
  apply StatMech.FK.boxVertIncl_boxOrigin n

/--
[connToBdry_succ_of_connToBdry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma connToBdry_succ_of_connToBdry_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : boxVerts d (n+1)}
-- given
  (hn : 1 ≤ n)
  (hv : boxBoundary d (n+1) v)
  (h : (openSub (boxGraph d (n+1)) (boxRestrict d (n+1) ω)).Reachable (IsingFK.boxOrigin d (n+1)) v) :
-- imply
  ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.FK.connToBdry_succ_of_connToBdry n hn ω hv h

/--
[boxBdryConnEvent_succ_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConnEvent_succ_subset_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  boxBdryConnEvent d (n+1) ⊆ boxBdryConnEvent d n := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_succ_subset n hn

/--
[wiredFiniteMeasure_boxBdryConnEvent_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_boxBdryConnEvent_antitone_eq
  {d : ℕ}
  {n : ℕ}
  {p : ℝ}
-- given
  (hn : 1 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d (n+1)) ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_boxBdryConnEvent_antitone n hn hp hp1

/--
[edgeIncl_innerEdgeLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma edgeIncl_innerEdgeLE_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
  {e : Sym2 (boxVerts d n)}
-- given
  (h : n ≤ m) :
-- imply
  edgeIncl d m (innerEdgeLE d h e) = edgeIncl d n e := by
-- proof
  apply StatMech.FK.edgeIncl_innerEdgeLE d h e

/--
[boxRestrictLE_boxRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxRestrictLE_boxRestrict_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : n ≤ m) :
-- imply
  boxRestrictLE d h (boxRestrict d m ω) = boxRestrict d n ω := by
-- proof
  apply StatMech.FK.boxRestrictLE_boxRestrict d h ω

/--
[boxRestrictLE_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxRestrictLE_monotone_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
-- given
  (h : n ≤ m) :
-- imply
  Monotone (boxRestrictLE d h) := by
-- proof
  apply StatMech.FK.boxRestrictLE_monotone d h

/--
[isIncreasing_connToBdryEventLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma isIncreasing_connToBdryEventLE_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
-- given
  (h : n ≤ m) :
-- imply
  IsIncreasing (connToBdryEventLE d h) := by
-- proof
  apply StatMech.FK.isIncreasing_connToBdryEventLE d h

/--
[boxBdryConnEvent_eq_boxRestrict_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConnEvent_eq_boxRestrict_preimage_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
-- given
  (h : n ≤ m) :
-- imply
  boxBdryConnEvent d n = boxRestrict d m ⁻¹' (connToBdryEventLE d h) := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_eq_boxRestrict_preimage d h

/--
[measurableSet_boxRestrict_connToBdryEventLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma measurableSet_boxRestrict_connToBdryEventLE_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
-- given
  (h : n ≤ m) :
-- imply
  MeasurableSet (boxRestrict d m ⁻¹' (connToBdryEventLE d h)) := by
-- proof
  apply StatMech.FK.measurableSet_boxRestrict_connToBdryEventLE d h

/--
[wiredFiniteMeasure_real_boxRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxRestrictEvent_eq
  {d : ℕ}
  {m : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S) = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)), S.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 S hmeas

/--
[wiredFiniteMeasure_succ_le_boxBdryConnEvent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_succ_le_boxBdryConnEvent_le_eq
  {d : ℕ}
  {n m : ℕ}
  {p : ℝ}
-- given
  (h : n ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_succ_le_boxBdryConnEvent_le n m h hp hp1

/--
[wiredFiniteMeasure_boxBdryConnEvent_antitone_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_boxBdryConnEvent_antitone_radius_eq
  {d : ℕ}
  {n k : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (n+k+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) ≤ (wiredFiniteMeasure d (n+k) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_boxBdryConnEvent_antitone_radius n k hp hp1

/--
[openSubgraph_adj_of_boxGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma openSubgraph_adj_of_boxGraph_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : boxVerts d n}
-- given
  (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y) :
-- imply
  (openSubgraph d ω).Adj (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FK.openSubgraph_adj_of_boxGraph n ω h

/--
[connected_of_boxConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma connected_of_boxConnected_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : boxVerts d n}
-- given
  (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable x y) :
-- imply
  StatMech.Lattice.Connected d ω (x : Site d) (y : Site d) := by
-- proof
  apply StatMech.FK.connected_of_boxConnected n ω h

/--
[boxBdryConnEvent_subset_crossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConnEvent_subset_crossingEvent_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  boxBdryConnEvent d n ⊆ crossingEvent d n := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_subset_crossingEvent n

/--
[boxGraph_open_of_openSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxGraph_open_of_openSubgraph_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : boxVerts d n}
-- given
  (h : (openSubgraph d ω).Adj (x : Site d) (y : Site d)) :
-- imply
  (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
-- proof
  apply StatMech.FK.boxGraph_open_of_openSubgraph n ω h

/--
[boxBdryConn_of_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConn_of_crossing_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
-- given
  (hn : 1 ≤ n)
  (hv : v ∉ box d n)
  (h : (openSubgraph d ω).Reachable (origin d) v) :
-- imply
  ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
-- proof
  apply StatMech.FK.boxBdryConn_of_crossing n hn ω hv h

/--
[crossingEvent_succ_subset_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma crossingEvent_succ_subset_boxBdryConnEvent_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  crossingEvent d (n+1) ⊆ boxBdryConnEvent d n := by
-- proof
  apply StatMech.FK.crossingEvent_succ_subset_boxBdryConnEvent n hn

/--
[wiredIv_boxBdryConnEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredIv_boxBdryConnEvent_tendsto_eq
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  Tendsto (fun n => ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)) atTop (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
-- proof
  apply StatMech.FK.wiredIv_boxBdryConnEvent_tendsto hp hp1 hq

/--
[boxBdryConnEvent_subset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConnEvent_subset_le_eq
  {d : ℕ}
  {k n : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkn : k ≤ n) :
-- imply
  boxBdryConnEvent d n ⊆ boxBdryConnEvent d k := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_subset_le k n hk hkn

/--
[radius_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma radius_antitone_eq
  {d : ℕ}
  {k : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Antitone (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) := by
-- proof
  apply StatMech.FK.radius_antitone k hp hp1

/--
[tendsto_of_antitone_of_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma tendsto_of_antitone_of_subseq_eq
  {d : ℕ}
  {a : ℕ → ℝ}
  {L : ℝ}
  {φ : ℕ → ℕ}
-- given
  (hφ : StrictMono φ)
  (hanti : Antitone a)
  (hbdd : BddBelow (Set.range a))
  (hsub : Tendsto (fun m => a (φ m)) atTop (𝓝 L)) :
-- imply
  Tendsto a atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.tendsto_of_antitone_of_subseq hφ hanti hbdd hsub

/--
[wiredFiniteMeasure_radius_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma wiredFiniteMeasure_radius_tendsto_eq
  {d : ℕ}
  {k : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) atTop (𝓝 (((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))) := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_radius_tendsto k hp hp1

/--
[boxBdryConnEvent_diag_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBdryConnEvent_diag_tendsto_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)) atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_diag_tendsto hp hp1

/--
[boxBoundaryConnProfile_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean)
-/
@[path]
private lemma boxBoundaryConnProfile_tendsto_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n) atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.FK.boxBoundaryConnProfile_tendsto hp hp1


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))), (innerRestrict d n ⁻¹' S).indicator (fun _ => (1 : ℝ)) ρ * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q ρ := by
-- proof
  apply StatMech.FK.fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1 hq S hmeas

/--
[fkgq_wiredFiniteMeasure_real_boxRestrictEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredFiniteMeasure_real_boxRestrictEvent_eq
  {d : ℕ}
  {m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S) = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)), S.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p q ω := by
-- proof
  apply StatMech.FK.fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 hq S hmeas

/--
[fkgq_wiredFiniteMeasure_succ_le_smallerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredFiniteMeasure_succ_le_smallerBox_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (wiredFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) ≤ ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.fkgq_wiredFiniteMeasure_succ_le_smallerBox n hp hp1 hq hS hmeas

/--
[fkgq_freeFiniteMeasure_smallerBox_le_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeFiniteMeasure_smallerBox_le_succ_eq
  {d : ℕ}
  {n : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S)
  (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
-- imply
  (∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p q ω) ≤ (freeFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkgq_freeFiniteMeasure_smallerBox_le_succ n hp hp1 hq hS hmeas

/--
[fkgq_free_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_succ_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) ≤ (freeFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkgq_free_succ N m hNm hp hp1 hq hS

/--
[fkgq_wired_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_succ_eq
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  (wiredFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) ≤ (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fkgq_wired_succ N m hNm hp hp1 hq hS

/--
[fkgq_free_infinite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_infinite_measure_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S)) atTop (nhds ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.fkgq_free_infinite_measure N hp hp1 hq hS

/--
[fkgq_wired_infinite_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_infinite_measure_eq
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hS : IsIncreasing S) :
-- imply
  Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S)) atTop (nhds ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' S))) := by
-- proof
  apply StatMech.FK.fkgq_wired_infinite_measure N hp hp1 hq hS

/--
[fkgq_ivp_eq_edgeFE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_ivp_eq_edgeFE_eq
  {d : ℕ}
  {d n : ℕ}
  {s q : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  ivp2_tiltFreeEnergy (boxGraph d n) q s = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 + StatMech.Walls.fkc_edgeFreeEnergy d s q n := by
-- proof
  apply StatMech.FK.fkgq_ivp_eq_edgeFE d n s q hq hE

/--
[fkgq_centered_eq_edgeFE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_centered_eq_edgeFE_eq
  {d : ℕ}
  {d n : ℕ}
  {s q : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < (boxGraph d n).edgeFinset.card) :
-- imply
  cfe_centered (boxGraph d n) q s = StatMech.Walls.fkc_edgeFreeEnergy d s q n - StatMech.Walls.fkc_edgeFreeEnergy d 0 q n := by
-- proof
  apply StatMech.FK.fkgq_centered_eq_edgeFE d n s q hq hE

/--
[fkgq_centeredConvergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_centeredConvergence_eq
  {d : ℕ}
  {d : ℕ}
  {q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  ∃ G : ℝ → ℝ, (∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s))) ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
-- proof
  apply StatMech.FK.fkgq_centeredConvergence d hd q hq

/--
[fkgq_avgDensity_eq_sum_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_avgDensity_eq_sum_edgeMarg_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q s : ℝ} :
-- imply
  fkgq_avgDensity G q s = (1 / (G.edgeFinset.card : ℝ)) * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic s) q) e := by
-- proof
  apply StatMech.FK.fkgq_avgDensity_eq_sum_edgeMarg G q s

/--
[fkgq_freeBulkCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeBulkCollapse_n1_eq
  {d : ℕ}
  {q s : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hq : 0 < q)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (nhds 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic s) q) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q s) atTop (nhds L) := by
-- proof
  apply StatMech.FK.fkgq_freeBulkCollapse_n1 q s hq hbox1 L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[fkgq_wiredBulkCollapse_n1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredBulkCollapse_n1_eq
  {d : ℕ}
  {q s : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hq : 0 < q)
  (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (nhds 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic s) q) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q s) atTop (nhds L) := by
-- proof
  apply StatMech.FK.fkgq_wiredBulkCollapse_n1 q s hq hbox1 L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[fkgq_centered_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_centered_hasDerivAt_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (cfe_centered G q) (fkgq_avgDensity G q s) s := by
-- proof
  apply StatMech.FK.fkgq_centered_hasDerivAt G q hq hE s

/--
[fkgq_wiredCentered_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredCentered_hasDerivAt_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : ℝ}
  {s : ℝ}
-- given
  (bdry : V → Prop)
  (hq : 0 < q)
  (hE : 0 < G.edgeFinset.card) :
-- imply
  HasDerivAt (cfe_wiredCentered G bdry q) (wpd_avgWiredDensity G bdry q s) s := by
-- proof
  apply StatMech.FK.fkgq_wiredCentered_hasDerivAt G bdry q hq hE s

/--
[fkgq_wiredCentered_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredCentered_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {q : ℝ}
  {G : ℝ → ℝ}
  {s : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s))) :
-- imply
  Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) q s) atTop (nhds (G s)) := by
-- proof
  apply StatMech.FK.fkgq_wiredCentered_tendsto d hd q hq s hfree

/--
[fkgq_freeMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeMass_nonneg_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 ≤ fkgq_freeMass d N q hq s := by
-- proof
  apply StatMech.FK.fkgq_freeMass_nonneg d N q hq s

/--
[fkgq_wiredMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredMass_nonneg_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  0 ≤ fkgq_wiredMass d N q hq s := by
-- proof
  apply StatMech.FK.fkgq_wiredMass_nonneg d N q hq s

/--
[fkgq_freeMass_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeMass_sum_one_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  ∑ ω, fkgq_freeMass d N q hq s ω = 1 := by
-- proof
  apply StatMech.FK.fkgq_freeMass_sum_one d N q hq s

/--
[fkgq_wiredMass_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredMass_sum_one_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  ∑ ω, fkgq_wiredMass d N q hq s ω = 1 := by
-- proof
  apply StatMech.FK.fkgq_wiredMass_sum_one d N q hq s

/--
[fkgq_eventMass_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_eventMass_free_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hq : 1 ≤ q) :
-- imply
  eventMassProb (fkgq_freeMass d N q hq s) A = (freeInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s) (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fkgq_eventMass_free d N q hq s A

/--
[fkgq_eventMass_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_eventMass_wired_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hq : 1 ≤ q) :
-- imply
  eventMassProb (fkgq_wiredMass d N q hq s) A = (wiredInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s) (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fkgq_eventMass_wired d N q hq s A

/--
[fkgq_edgeMarg_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_edgeMarg_free_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
  {e : Sym2 (boxVerts d N)}
-- given
  (hq : 1 ≤ q) :
-- imply
  edgeMargProb (fkgq_freeMass d N q hq s) e = freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
-- proof
  apply StatMech.FK.fkgq_edgeMarg_free d N q hq s e

/--
[fkgq_edgeMarg_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_edgeMarg_wired_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
  {e : Sym2 (boxVerts d N)}
-- given
  (hq : 1 ≤ q) :
-- imply
  edgeMargProb (fkgq_wiredMass d N q hq s) e = wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
-- proof
  apply StatMech.FK.fkgq_edgeMarg_wired d N q hq s e

/--
[fkgq_freeIV_le_wiredIV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeIV_le_wiredIV_eq
  {d : ℕ}
  {d N : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fkgq_freeIV_le_wiredIV d N hp hp1 hq hA

/--
[fkgq_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_dominated_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
  {s : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  measOfMass (fkgq_freeMass d N q hq s) ≼ measOfMass (fkgq_wiredMass d N q hq s) := by
-- proof
  apply StatMech.FK.fkgq_dominated d N q hq s

/--
[fkgq_hcoup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_hcoup_eq
  {d : ℕ}
  {d N : ℕ}
  {q : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  ∀ s : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ, IsMonotoneCouplingFun P (fkgq_freeMass d N q hq s) (fkgq_wiredMass d N q hq s) := by
-- proof
  apply StatMech.FK.fkgq_hcoup d N q hq

/--
[fkgq_free_finite_mass_eq_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_finite_mass_eq_edgeMarg_eq
  {d : ℕ}
  {N m : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (freeFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = edgeMargProb (fkProb (boxGraph d m) p q) (innerEdgeLE d hNm e) := by
-- proof
  apply StatMech.FK.fkgq_free_finite_mass_eq_edgeMarg N m hNm e hp hp1 hq

/--
[fkgq_wired_finite_mass_eq_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_finite_mass_eq_edgeMarg_eq
  {d : ℕ}
  {N m : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (wiredFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) (innerEdgeLE d hNm e) := by
-- proof
  apply StatMech.FK.fkgq_wired_finite_mass_eq_edgeMarg N m hNm e hp hp1 hq

/--
[fkgq_free_density_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_eq_limit_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p q) (innerEdgeLE d (Nat.le_add_right N k) e)) atTop (nhds (freeEdgeDensity d q (edgeIncl d N e) p)) := by
-- proof
  apply StatMech.FK.fkgq_free_density_eq_limit N e hp hp1 hq

/--
[fkgq_wired_density_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_density_eq_limit_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q) (innerEdgeLE d (Nat.le_add_right N k) e)) atTop (nhds (wiredEdgeDensity d q (edgeIncl d N e) p)) := by
-- proof
  apply StatMech.FK.fkgq_wired_density_eq_limit N e hp hp1 hq

/--
[fkgq_box_free_edgeMarg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_box_free_edgeMarg_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {m : ℕ}
  {p q : ℝ}
  {e : Sym2 (boxVerts d m)} :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p q) (Sym2.map (S.lift m) e) = edgeMargProb (fkProb (boxGraph d m) p q) e := by
-- proof
  apply StatMech.FK.fkgq_box_free_edgeMarg_inv S m p q e

/--
[fkgq_box_wired_edgeMarg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_box_wired_edgeMarg_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {m : ℕ}
  {p q : ℝ}
  {e : Sym2 (boxVerts d m)} :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) (Sym2.map (S.lift m) e) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) e := by
-- proof
  apply StatMech.FK.fkgq_box_wired_edgeMarg_inv S m p q e

/--
[fkgq_free_density_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) p = freeEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
-- proof
  apply StatMech.FK.fkgq_free_density_boxSym S N e hp hp1 hq

/--
[fkgq_wired_density_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_density_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (edgeIncl d N e) p = wiredEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
-- proof
  apply StatMech.FK.fkgq_wired_density_boxSym S N e hp hp1 hq

/--
[fkgq_free_per_edge_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_per_edge_upper_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  edgeMargProb (fkProb (boxGraph d n) p q) e ≤ freeEdgeDensity d q (edgeIncl d n e) p := by
-- proof
  apply StatMech.FK.fkgq_free_per_edge_upper n e hp hp1 hq

/--
[fkgq_wired_per_edge_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_per_edge_lower_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (boxVerts d n)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (edgeIncl d n e) p ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) e := by
-- proof
  apply StatMech.FK.fkgq_wired_per_edge_lower n e hp hp1 hq

/--
[fkgq_free_offCentre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_offCentre_lower_eq
  {d : ℕ}
  {R n : ℕ}
  {u v : boxVerts d (n - R)}
  {p q : ℝ}
-- given
  (hRn : R ≤ n)
  (hmn : n - R ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (c0 : (0 : Site d) ∈ box d R)
  (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
-- imply
  edgeMargProb (fkProb (boxGraph d R) p q) (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) ≤ edgeMargProb (fkProb (boxGraph d n) p q) (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R)))) := by
-- proof
  apply StatMech.FK.fkgq_free_offCentre_lower R n hRn hmn u v hp hp1 hq c0 cw

/--
[fkgq_wired_offCentre_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_offCentre_upper_eq
  {d : ℕ}
  {R n : ℕ}
  {u v : boxVerts d (n - R - 1)}
  {p q : ℝ}
-- given
  (hR : 1 ≤ R)
  (hRn1 : R + 1 ≤ n)
  (hmn : n - R - 1 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (c0 : (0 : Site d) ∈ box d R)
  (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R - 1)))) ≤ edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p q) (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) := by
-- proof
  apply StatMech.FK.fkgq_wired_offCentre_upper R n hR hRn1 hmn u v hp hp1 hq c0 cw

/--
[fkgq_transBox_subset_box_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_transBox_subset_box_add_eq
  {d : ℕ}
  {m : ℕ}
  {a : Site d} :
-- imply
  fvs_transBox d m a ⊆ box d (m + Finset.univ.sup (fun i => (a i).natAbs)) := by
-- proof
  apply StatMech.FK.fkgq_transBox_subset_box_add m a

/--
[fkgq_density_translate_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_density_translate_order_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {a : Site d}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N eb) p ≤ freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p ∧ wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p ≤ wiredEdgeDensity d q (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.fkgq_density_translate_order N eb a hp hp1 hq

/--
[fkgq_density_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_density_translation_inv_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {a : Site d}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N eb) p = freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p ∧ wiredEdgeDensity d q (edgeIncl d N eb) p = wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p := by
-- proof
  apply StatMech.FK.fkgq_density_translation_inv N eb a hp hp1 hq

/--
[fkgq_free_density_boxSym_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_boxSym_lattice_eq
  {d : ℕ}
  {S : BoxSym d}
  {e : Sym2 (Site d)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (Sym2.map S.τ e) p = freeEdgeDensity d q e p := by
-- proof
  apply StatMech.FK.fkgq_free_density_boxSym_lattice S e hp hp1 hq

/--
[fkgq_wired_density_boxSym_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_density_boxSym_lattice_eq
  {d : ℕ}
  {S : BoxSym d}
  {e : Sym2 (Site d)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (Sym2.map S.τ e) p = wiredEdgeDensity d q e p := by
-- proof
  apply StatMech.FK.fkgq_wired_density_boxSym_lattice S e hp hp1 hq

/--
[fkgq_density_translation_inv_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_density_translation_inv_lattice_eq
  {d : ℕ}
  {e : Sym2 (Site d)}
  {a : Site d}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q e p = freeEdgeDensity d q (Sym2.map (fun x => x + a) e) p ∧ wiredEdgeDensity d q e p = wiredEdgeDensity d q (Sym2.map (fun x => x + a) e) p := by
-- proof
  apply StatMech.FK.fkgq_density_translation_inv_lattice e a hp hp1 hq

/--
[fkgq_free_density_recentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_recentre_eq
  {d : ℕ}
  {x y : Site d}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
-- proof
  apply StatMech.FK.fkgq_free_density_recentre x y hp hp1 hq

/--
[fkgq_wired_density_recentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_density_recentre_eq
  {d : ℕ}
  {x y : Site d}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
-- proof
  apply StatMech.FK.fkgq_wired_density_recentre x y hp hp1 hq

/--
[fkgq_free_centred_unit_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_centred_unit_const_eq
  {d : ℕ}
  {j : Fin d}
  {b : Bool}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_free_centred_unit_const hd j b hp hp1 hq

/--
[fkgq_wired_centred_unit_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_centred_unit_const_eq
  {d : ℕ}
  {j : Fin d}
  {b : Bool}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_wired_centred_unit_const hd j b hp hp1 hq

/--
[fkgq_free_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_edge_const_eq
  {d : ℕ}
  {x y : Site d}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (hadj : (hypercubicLattice d).Adj x y)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_free_edge_const hd x y hadj hp hp1 hq

/--
[fkgq_wired_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_edge_const_eq
  {d : ℕ}
  {x y : Site d}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (hadj : (hypercubicLattice d).Adj x y)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_wired_edge_const hd x y hadj hp hp1 hq

/--
[fkgq_free_box_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_box_edge_const_eq
  {d : ℕ}
  {m : ℕ}
  {eb : Sym2 (boxVerts d m)}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d m eb) p = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_free_box_edge_const hd m eb heb hp hp1 hq

/--
[fkgq_wired_box_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_box_edge_const_eq
  {d : ℕ}
  {m : ℕ}
  {eb : Sym2 (boxVerts d m)}
  {p q : ℝ}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (edgeIncl d m eb) p = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.fkgq_wired_box_edge_const hd m eb heb hp hp1 hq

/--
[fkgq_fkExpect_openCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_fkExpect_openCount_eq_sum_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ} :
-- imply
  fkExpect G p q (fun ω => (openCount G ω : ℝ)) = ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G p q) e := by
-- proof
  apply StatMech.FK.fkgq_fkExpect_openCount_eq_sum G p q

/--
[fkgq_avgDensity_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_avgDensity_eq_sum_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q t : ℝ} :
-- imply
  fkgq_avgDensity G q t = (1 / (G.edgeFinset.card : ℝ)) * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic t) q) e := by
-- proof
  apply StatMech.FK.fkgq_avgDensity_eq_sum G q t

/--
[fkgq_free_avg_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_avg_collapse_eq
  {d : ℕ}
  {q t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hq : 1 ≤ q)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (nhds 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop (nhds L) := by
-- proof
  apply StatMech.FK.fkgq_free_avg_collapse q t hq hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[fkgq_wired_avg_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_avg_collapse_eq
  {d : ℕ}
  {q t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hq : 1 ≤ q)
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (nhds 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop (nhds L) := by
-- proof
  apply StatMech.FK.fkgq_wired_avg_collapse q t hq hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[fkgq_unitMarg_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_unitMarg_tendsto_eq
  {d : ℕ}
  {q : ℝ}
  {dir : Fin d × Bool}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => fkgq_unitMarg d q n dir t) atTop (nhds (freeEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.fkgq_unitMarg_tendsto q hq dir t

/--
[fkgq_unitWiredMarg_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_unitWiredMarg_tendsto_eq
  {d : ℕ}
  {q : ℝ}
  {dir : Fin d × Bool}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => fkgq_unitWiredMarg d q n dir t) atTop (nhds (wiredEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.fkgq_unitWiredMarg_tendsto q hq dir t

/--
[fkgq_freeDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeDelta_nonneg_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q t : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ fkgq_freeDelta N e q t n := by
-- proof
  apply StatMech.FK.fkgq_freeDelta_nonneg N e q t n

/--
[fkgq_wiredDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredDelta_nonneg_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q t : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ fkgq_wiredDelta N e q t n := by
-- proof
  apply StatMech.FK.fkgq_wiredDelta_nonneg N e q t n

/--
[fkgq_freeDelta_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeDelta_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (he : e ∈ (boxGraph d N).edgeFinset)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => fkgq_freeDelta N e q t n) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.fkgq_freeDelta_tendsto_zero hd N e he q hq t

/--
[fkgq_wiredDelta_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredDelta_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (he : e ∈ (boxGraph d N).edgeFinset)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => fkgq_wiredDelta N e q t n) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.fkgq_wiredDelta_tendsto_zero hd N e he q hq t

/--
[fkgq_freeDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_freeDensity_mem_Icc_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.FK.fkgq_freeDensity_mem_Icc N e q hq t

/--
[fkgq_wiredDensity_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wiredDensity_mem_Icc_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.FK.fkgq_wiredDensity_mem_Icc N e q hq t

/--
[fkgq_free_bulk_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_bulk_lower_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
  {n : ℕ}
  {u v : boxVerts d (n - Nat.sqrt n)}
-- given
  (hq : 1 ≤ q)
  (hn : 1 ≤ n)
  (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) - fkgq_freeDelta N e q t n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
-- proof
  apply StatMech.FK.fkgq_free_bulk_lower N e q hq t n hn u v hadj

/--
[fkgq_wired_bulk_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_bulk_upper_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
  {n : ℕ}
  {u v : boxVerts d (n - Nat.sqrt n - 1)}
-- given
  (hq : 1 ≤ q)
  (hn : 2 ≤ n)
  (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))) (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1)))) ≤ wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) + fkgq_wiredDelta N e q t n := by
-- proof
  apply StatMech.FK.fkgq_wired_bulk_upper N e q hq t n hn u v hadj

/--
[fkgq_genuineFreeCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_genuineFreeCollapse_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (he : e ∈ (boxGraph d N).edgeFinset)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop (nhds (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.fkgq_genuineFreeCollapse hd N e he q hq t

/--
[fkgq_genuineWiredCollapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_genuineWiredCollapse_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {q : ℝ}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (he : e ∈ (boxGraph d N).edgeFinset)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop (nhds (wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
-- proof
  apply StatMech.FK.fkgq_genuineWiredCollapse hd N e he q hq t

/--
[fkgq_free_density_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_nonEdge_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (he : e ∉ (boxGraph d N).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
-- proof
  apply StatMech.FK.fkgq_free_density_nonEdge N e he hp hp1 hq

/--
[fkgq_wired_density_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_wired_density_nonEdge_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (he : e ∉ (boxGraph d N).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  wiredEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
-- proof
  apply StatMech.FK.fkgq_wired_density_nonEdge N e he hp hp1 hq

/--
[fkgq_free_density_le_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_free_density_le_wired_eq
  {d : ℕ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) p ≤ wiredEdgeDensity d q (edgeIncl d N e) p := by
-- proof
  apply StatMech.FK.fkgq_free_density_le_wired N e hp hp1 hq

/--
[fkgq_centered_deriv_eq_densities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_centered_deriv_eq_densities_eq
  {d : ℕ}
  {q : ℝ}
  {G : ℝ → ℝ}
  {N : ℕ}
  {e : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q)
  (hG : ConvexOn ℝ Set.univ G)
  (hlim : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)))
  (he : e ∈ (boxGraph d N).edgeFinset)
  (hdiff : pressureLeftDeriv G t = pressureRightDeriv G t) :
-- imply
  freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureLeftDeriv G t ∧ wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureRightDeriv G t := by
-- proof
  apply StatMech.FK.fkgq_centered_deriv_eq_densities hd q hq hG hlim N e he t hdiff

/--
[fkgq_countable_free_wired_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean)
-/
@[path]
private lemma fkgq_countable_free_wired_disagreement_eq
  {d : ℕ}
  {N : ℕ}
  {q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hq : 1 ≤ q) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fkgq_freeMass d N q hq t) A ≠ eventMassProb (fkgq_wiredMass d N q hq t) A}.Countable := by
-- proof
  apply StatMech.FK.fkgq_countable_free_wired_disagreement hd N q hq


-- created on 2026-10-23

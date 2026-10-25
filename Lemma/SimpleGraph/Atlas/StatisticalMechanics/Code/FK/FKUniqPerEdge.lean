import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
open Set Filter Topology StatMech.FK StatMech


/--
[fpe2_edgeProduct_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_edgeProduct_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
-- proof
  apply StatMech.FK.fpe2_edgeProduct_toggle_invariant he ω

/--
[fpe2_fkWeight_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_fkWeight_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fpe2_fkWeight_toggle_invariant he ω

/--
[fpe2_fkProb_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_fkProb_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (he : e ∉ G.edgeFinset) :
-- imply
  fkProb G p q (setOpen e ω) = fkProb G p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fpe2_fkProb_toggle_invariant he ω

/--
[fpe2_wiredFkWeight_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_wiredFkWeight_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (he : e ∉ G.edgeFinset) :
-- imply
  wiredFkWeight G bdry p q (setOpen e ω) = wiredFkWeight G bdry p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fpe2_wiredFkWeight_toggle_invariant bdry he ω

/--
[fpe2_wiredFkProb_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_wiredFkProb_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
  {p q : ℝ}
  {e : Sym2 V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (he : e ∉ G.edgeFinset) :
-- imply
  wiredFkProb G bdry p q (setOpen e ω) = wiredFkProb G bdry p q (setClosed e ω) := by
-- proof
  apply StatMech.FK.fpe2_wiredFkProb_toggle_invariant bdry he ω

/--
[fpe2_edgeMargProb_eq_openFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_edgeMargProb_eq_openFiber_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V} :
-- imply
  edgeMargProb μ e = ∑ ω ∈ Finset.univ.filter (fun ω : ConfigSpace (Sym2 V) => ω e = true), μ ω := by
-- proof
  apply StatMech.FK.fpe2_edgeMargProb_eq_openFiber μ e

/--
[fpe2_edgeMargProb_eq_closedFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_edgeMargProb_eq_closedFiber_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V} :
-- imply
  edgeMargProb μ e = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false), μ (setOpen e ψ) := by
-- proof
  apply StatMech.FK.fpe2_edgeMargProb_eq_closedFiber μ e

/--
[fpe2_closedFiber_pairMass_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_closedFiber_pairMass_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V} :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace (Sym2 V) => ψ e = false), (μ (setOpen e ψ) + μ (setClosed e ψ)) = ∑ ω, μ ω := by
-- proof
  apply StatMech.FK.fpe2_closedFiber_pairMass_eq_sum μ e

/--
[fpe2_edgeMargProb_half_of_toggle_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_edgeMargProb_half_of_toggle_invariant_eq
  [Fintype V]
  [DecidableEq V]
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (hsum : ∑ ω, μ ω = 1)
  (hinv : ∀ ψ : ConfigSpace (Sym2 V), μ (setOpen e ψ) = μ (setClosed e ψ)) :
-- imply
  edgeMargProb μ e = 1 / 2 := by
-- proof
  apply StatMech.FK.fpe2_edgeMargProb_half_of_toggle_invariant μ e hsum hinv

/--
[fpe2_innerEdgeLE_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_innerEdgeLE_mk_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N m : ℕ}
  {u v : boxVerts d N}
-- given
  (hNm : N ≤ m) :
-- imply
  innerEdgeLE d hNm (s(u, v) : Sym2 (boxVerts d N)) = s(boxVertInclLE d hNm u, boxVertInclLE d hNm v) := by
-- proof
  apply StatMech.FK.fpe2_innerEdgeLE_mk N m hNm u v

/--
[fpe2_innerEdgeLE_notMem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_innerEdgeLE_notMem_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N m : ℕ}
  {e' : Sym2 (boxVerts d N)}
-- given
  (hNm : N ≤ m)
  (he' : e' ∉ (boxGraph d N).edgeFinset) :
-- imply
  innerEdgeLE d hNm e' ∉ (boxGraph d m).edgeFinset := by
-- proof
  apply StatMech.FK.fpe2_innerEdgeLE_notMem_edgeFinset N m hNm e' he'

/--
[fpe2_free_finite_marg_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_free_finite_marg_nonEdge_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {m : ℕ}
  {e : Sym2 (boxVerts d m)}
  {p : ℝ}
-- given
  (he : e ∉ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p 2) e = 1 / 2 := by
-- proof
  apply StatMech.FK.fpe2_free_finite_marg_nonEdge m e he hp hp1

/--
[fpe2_wired_finite_marg_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_wired_finite_marg_nonEdge_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {m : ℕ}
  {e : Sym2 (boxVerts d m)}
  {p : ℝ}
-- given
  (he : e ∉ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e = 1 / 2 := by
-- proof
  apply StatMech.FK.fpe2_wired_finite_marg_nonEdge m e he hp hp1

/--
[fpe2_free_density_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_free_density_nonEdge_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (he' : e' ∉ (boxGraph d N).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
-- proof
  apply StatMech.FK.fpe2_free_density_nonEdge N e' he' hp hp1

/--
[fpe2_wired_density_nonEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_wired_density_nonEdge_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (he' : e' ∉ (boxGraph d N).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N e') p = 1 / 2 := by
-- proof
  apply StatMech.FK.fpe2_wired_density_nonEdge N e' he' hp hp1

/--
[fpe2_halfLin_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_halfLin_rightDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {t : ℝ} :
-- imply
  pressureRightDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
-- proof
  apply StatMech.FK.fpe2_halfLin_rightDeriv t

/--
[fpe2_halfLin_leftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_halfLin_leftDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {t : ℝ} :
-- imply
  pressureLeftDeriv (fun s : ℝ => (1/2) * s) t = 1/2 := by
-- proof
  apply StatMech.FK.fpe2_halfLin_leftDeriv t

/--
[fpe2_halfLin_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_halfLin_convex_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ} :
-- imply
  ConvexOn ℝ univ (fun s : ℝ => (1/2) * s) := by
-- proof
  apply StatMech.FK.fpe2_halfLin_convex

/--
[fpe2_perEdgeG_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_perEdgeG_convex_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {d N : ℕ}
  {G : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
-- given
  (hG : ConvexOn ℝ univ G) :
-- imply
  ConvexOn ℝ univ (fpe2_perEdgeG d N G e') := by
-- proof
  apply StatMech.FK.fpe2_perEdgeG_convex d N hG e'

/--
[fpe2_ha_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_ha_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {d N : ℕ}
  {G : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hfree : fpe2_GenuineFreeIsLeftDeriv d N G) :
-- imply
  edgeMargProb (fuc_freeMass d N t) e' = pressureLeftDeriv (fpe2_perEdgeG d N G e') t := by
-- proof
  apply StatMech.FK.fpe2_ha_eq d N hfree e' t

/--
[fpe2_hb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_hb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {d N : ℕ}
  {G : ℝ → ℝ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hwired : fpe2_GenuineWiredIsRightDeriv d N G) :
-- imply
  edgeMargProb (fuc_wiredMass d N t) e' = pressureRightDeriv (fpe2_perEdgeG d N G e') t := by
-- proof
  apply StatMech.FK.fpe2_hb_eq d N hwired e' t

/--
[fpe2_wired_genuine_eq_ref](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_wired_genuine_eq_ref_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {eb e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (he' : e' ∈ (boxGraph d N).edgeFinset)
  (heb : eb ∈ (boxGraph d N).edgeFinset) :
-- imply
  edgeMargProb (fuc_wiredMass d N t) e' = edgeMargProb (fuc_wiredMass d N t) eb := by
-- proof
  apply StatMech.FK.fpe2_wired_genuine_eq_ref hd N he' heb t

/--
[fpe2_hlink](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_hlink_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d N).edgeFinset) :
-- imply
  ∀ t : ℝ, ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) eb) t → ∀ e' : Sym2 (boxVerts d N), ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) e') t := by
-- proof
  apply StatMech.FK.fpe2_hlink hd N eb heb

/--
[fpe2_fk_uniqueness_of_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_fk_uniqueness_of_genuine_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {G : ℝ → ℝ}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hG : ConvexOn ℝ univ G)
  (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
  (hwired : fpe2_GenuineWiredIsRightDeriv d N G) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fpe2_fk_uniqueness_of_genuine hd N eb heb hG hfree hwired

/--
[fpe2_genuineFreeIsLeftDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_genuineFreeIsLeftDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcol : fpe2_GenuineFreeCollapse d N) :
-- imply
  fpe2_GenuineFreeIsLeftDeriv d N g := by
-- proof
  apply StatMech.FK.fpe2_genuineFreeIsLeftDeriv N hEbox hg hboxfree hcol

/--
[fpe2_genuineWiredIsRightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_genuineWiredIsRightDeriv_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  fpe2_GenuineWiredIsRightDeriv d N g := by
-- proof
  apply StatMech.FK.fpe2_genuineWiredIsRightDeriv hd N hEbox hg hboxfree hcolfree hcolwired

/--
[fpe2_fk_uniqueness_of_boxFekete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_fk_uniqueness_of_boxFekete_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fpe2_fk_uniqueness_of_boxFekete hd N eb heb hEbox hg hboxfree hcolfree hcolwired

/--
[fpe2_fk_uniqueness_of_perVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_fk_uniqueness_of_perVolume_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (heb : eb ∈ (boxGraph d N).edgeFinset)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
  (hcolfree : fpe2_GenuineFreeCollapse d N)
  (hcolwired : fpe2_GenuineWiredCollapse d N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fpe2_fk_uniqueness_of_perVolume hd N eb heb hEbox hdata hcolfree hcolwired

/--
[fpe2_genuineFreeCollapse_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_genuineFreeCollapse_of_all_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
-- given
  (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
-- imply
  fpe2_GenuineFreeCollapse d N := by
-- proof
  apply StatMech.FK.fpe2_genuineFreeCollapse_of_all N hcol

/--
[fpe2_genuineWiredCollapse_of_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_genuineWiredCollapse_of_all_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
-- given
  (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
-- imply
  fpe2_GenuineWiredCollapse d N := by
-- proof
  apply StatMech.FK.fpe2_genuineWiredCollapse_of_all N hcol

/--
[fpe2_genuineFree_target_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean)
-/
@[path]
private lemma fpe2_genuineFree_target_const_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {N : ℕ}
  {e₁ e₂ : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (h0 : e₁ ∈ (boxGraph d N).edgeFinset)
  (h1 : e₂ ∈ (boxGraph d N).edgeFinset) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e₁) (fsc_logistic t) = freeEdgeDensity d 2 (edgeIncl d N e₂) (fsc_logistic t) := by
-- proof
  apply StatMech.FK.fpe2_genuineFree_target_const hd N h0 h1 t


-- created on 2026-10-23

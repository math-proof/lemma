import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
open SimpleGraph StatMech StatMech.FK


/--
[boxVertIncl_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma boxVertIncl_val_eq
  {d n : ℕ}
  {x : boxVerts d n} :
-- imply
  ((boxVertIncl d n x : boxVerts d (n+1)) : Site d) = (x : Site d) := by
-- proof
  apply StatMech.FK.boxVertIncl_val d n x

/--
[boxVertIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma boxVertIncl_injective_eq
  {d n : ℕ} :
-- imply
  Function.Injective (boxVertIncl d n) := by
-- proof
  apply StatMech.FK.boxVertIncl_injective d n

/--
[boxGraph_adj_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma boxGraph_adj_boxVertIncl_eq
  {d n : ℕ}
  {x y : boxVerts d n} :
-- imply
  (boxGraph d (n+1)).Adj (boxVertIncl d n x) (boxVertIncl d n y) ↔ (boxGraph d n).Adj x y := by
-- proof
  apply StatMech.FK.boxGraph_adj_boxVertIncl d n x y

/--
[boxGraph_eq_comap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma boxGraph_eq_comap_eq
  {d n : ℕ} :
-- imply
  boxGraph d n = (boxGraph d (n+1)).comap (boxVertIncl d n) := by
-- proof
  apply StatMech.FK.boxGraph_eq_comap d n

/--
[innerEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerEdge_injective_eq
  {d n : ℕ} :
-- imply
  Function.Injective (innerEdge d n) := by
-- proof
  apply StatMech.FK.innerEdge_injective d n

/--
[edgeIncl_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma edgeIncl_innerEdge_eq
  {d n : ℕ}
  {e : Sym2 (boxVerts d n)} :
-- imply
  edgeIncl d (n+1) (innerEdge d n e) = edgeIncl d n e := by
-- proof
  apply StatMech.FK.edgeIncl_innerEdge d n e

/--
[isInnerVert_iff_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma isInnerVert_iff_range_eq
  {d n : ℕ}
  {v : boxVerts d (n+1)} :
-- imply
  IsInnerVert d n v ↔ ∃ x, boxVertIncl d n x = v := by
-- proof
  apply StatMech.FK.isInnerVert_iff_range d n v

/--
[isInnerVert_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma isInnerVert_boxVertIncl_eq
  {d n : ℕ}
  {x : boxVerts d n} :
-- imply
  IsInnerVert d n (boxVertIncl d n x) := by
-- proof
  apply StatMech.FK.isInnerVert_boxVertIncl d n x

/--
[crossExt_innerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossExt_innerEdge_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (boxVerts d n)} :
-- imply
  crossExt d n ω (innerEdge d n e) = ω e := by
-- proof
  apply StatMech.FK.crossExt_innerEdge d n ω e

/--
[innerBdry_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerBdry_boxVertIncl_eq
  {d n : ℕ}
  {x : boxVerts d n} :
-- imply
  innerBdry d n (boxVertIncl d n x) ↔ boxBoundary d n x := by
-- proof
  apply StatMech.FK.innerBdry_boxVertIncl d n x

/--
[innerBdry_isInnerVert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerBdry_isInnerVert_eq
  {d n : ℕ}
  {v : boxVerts d (n+1)}
-- given
  (h : innerBdry d n v) :
-- imply
  IsInnerVert d n v := by
-- proof
  apply StatMech.FK.innerBdry_isInnerVert d n h

/--
[crossExt_open_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossExt_open_inner_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {u v : boxVerts d (n+1)}
-- given
  (h : crossExt d n ω s(u, v) = true) :
-- imply
  IsInnerVert d n u ∧ IsInnerVert d n v := by
-- proof
  apply StatMech.FK.crossExt_open_inner d n ω h

/--
[crossWiredGraph_not_adj_of_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_not_adj_of_annulus_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {v : boxVerts d (n+1)}
  {w : boxVerts d (n+1)}
-- given
  (hv : ¬ IsInnerVert d n v) :
-- imply
  ¬ (crossWiredGraph d n ω).Adj v w := by
-- proof
  apply StatMech.FK.crossWiredGraph_not_adj_of_annulus d n ω hv w

/--
[crossExt_innerEdge_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossExt_innerEdge_pair_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n} :
-- imply
  crossExt d n ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
-- proof
  apply StatMech.FK.crossExt_innerEdge_pair d n ω x y

/--
[crossWiredGraph_adj_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_adj_boxVertIncl_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n} :
-- imply
  (crossWiredGraph d n ω).Adj (boxVertIncl d n x) (boxVertIncl d n y) ↔ (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Adj x y := by
-- proof
  apply StatMech.FK.crossWiredGraph_adj_boxVertIncl d n ω x y

/--
[crossWiredGraph_adj_inner_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_adj_inner_right_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : IsInnerVert d n u)
  (h : (crossWiredGraph d n ω).Adj u w) :
-- imply
  IsInnerVert d n w := by
-- proof
  apply StatMech.FK.crossWiredGraph_adj_inner_right d n ω hu h

/--
[crossWiredGraph_reachable_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_reachable_inner_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {u w : boxVerts d (n+1)}
-- given
  (hu : IsInnerVert d n u)
  (h : (crossWiredGraph d n ω).Reachable u w) :
-- imply
  IsInnerVert d n w := by
-- proof
  apply StatMech.FK.crossWiredGraph_reachable_inner d n ω hu h

/--
[crossWiredGraph_reachable_of_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_reachable_of_inner_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n}
-- given
  (h : (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y) :
-- imply
  (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y) := by
-- proof
  apply StatMech.FK.crossWiredGraph_reachable_of_inner d n ω h

/--
[inner_reachable_of_crossWiredGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma inner_reachable_of_crossWiredGraph_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x y : boxVerts d n}
-- given
  (h : (crossWiredGraph d n ω).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (wiredGraph (boxGraph d n) (boxBoundary d n) ω).Reachable x y := by
-- proof
  apply StatMech.FK.inner_reachable_of_crossWiredGraph d n ω h

/--
[crossComponentEquivFun_inl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivFun_inl_mk_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {x : boxVerts d n} :
-- imply
  crossComponentEquivFun d n ω (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x)) = (crossWiredGraph d n ω).connectedComponentMk (boxVertIncl d n x) := by
-- proof
  apply StatMech.FK.crossComponentEquivFun_inl_mk d n ω x

/--
[crossWiredGraph_reachable_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraph_reachable_annulus_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {v w : boxVerts d (n+1)}
-- given
  (hv : ¬ IsInnerVert d n v)
  (h : (crossWiredGraph d n ω).Reachable v w) :
-- imply
  w = v := by
-- proof
  apply StatMech.FK.crossWiredGraph_reachable_annulus d n ω hv h

/--
[crossComponentEquivFun_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivFun_injective_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  Function.Injective (crossComponentEquivFun d n ω) := by
-- proof
  apply StatMech.FK.crossComponentEquivFun_injective d n ω

/--
[crossComponentEquivFun_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivFun_surjective_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  Function.Surjective (crossComponentEquivFun d n ω) := by
-- proof
  apply StatMech.FK.crossComponentEquivFun_surjective d n ω

/--
[numClustersWired_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma numClustersWired_crossExt_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  StatMech.Lattice.numClustersWired (boxGraph d (n+1)) (innerBdry d n) (crossExt d n ω) = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω + annulusCard d n := by
-- proof
  apply StatMech.FK.numClustersWired_crossExt d n ω

/--
[innerEdge_mem_edgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerEdge_mem_edgeSet_iff_eq
  {d n : ℕ}
  {e : Sym2 (boxVerts d n)} :
-- imply
  innerEdge d n e ∈ (boxGraph d (n+1)).edgeSet ↔ e ∈ (boxGraph d n).edgeSet := by
-- proof
  apply StatMech.FK.innerEdge_mem_edgeSet_iff d n e

/--
[innerEdge_image_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerEdge_image_edgeFinset_eq
  {d n : ℕ} :
-- imply
  (boxGraph d n).edgeFinset.image (innerEdge d n) = (boxGraph d (n+1)).edgeFinset.filter (· ∈ Set.range (innerEdge d n)) := by
-- proof
  apply StatMech.FK.innerEdge_image_edgeFinset d n

/--
[crossExt_eq_false_of_not_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossExt_eq_false_of_not_range_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {e : Sym2 (boxVerts d (n+1))}
-- given
  (he : e ∉ Set.range (innerEdge d n)) :
-- imply
  crossExt d n ω e = false := by
-- proof
  apply StatMech.FK.crossExt_eq_false_of_not_range d n ω he

/--
[edgeProduct_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma edgeProduct_crossExt_eq
  {d n : ℕ}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  edgeProduct (boxGraph d (n+1)) p (crossExt d n ω) = edgeProduct (boxGraph d n) p ω * (1 - p) ^ nonInnerEdgeCard d n := by
-- proof
  apply StatMech.FK.edgeProduct_crossExt d n ω

/--
[crossShift_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossShift_pos_eq
  {d n : ℕ}
  {p q : ℝ}
-- given
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < crossShift d n p q := by
-- proof
  apply StatMech.FK.crossShift_pos hp1 hq

/--
[bcWeight_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma bcWeight_crossExt_eq
  {d n : ℕ}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  bcWeight (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q (crossExt d n ω) = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShift d n p q := by
-- proof
  apply StatMech.FK.bcWeight_crossExt d n ω

/--
[mem_innerEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma mem_innerEdgeFinset_eq
  {d n : ℕ}
  {e : Sym2 (boxVerts d (n+1))} :
-- imply
  e ∈ innerEdgeFinset d n ↔ e ∈ Set.range (innerEdge d n) := by
-- proof
  apply StatMech.FK.mem_innerEdgeFinset d n e

/--
[innerRestrict_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma innerRestrict_crossExt_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  innerRestrict d n (crossExt d n ω) = ω := by
-- proof
  apply StatMech.FK.innerRestrict_crossExt d n ω

/--
[crossExt_innerRestrict_of_agreesOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossExt_innerRestrict_of_agreesOff_eq
  {d n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
-- given
  (hρ : AgreesOff (innerEdgeFinset d n) (fun _ => false) ρ) :
-- imply
  crossExt d n (innerRestrict d n ρ) = ρ := by
-- proof
  apply StatMech.FK.crossExt_innerRestrict_of_agreesOff d n hρ

/--
[agreesOff_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma agreesOff_crossExt_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  AgreesOff (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω) := by
-- proof
  apply StatMech.FK.agreesOff_crossExt d n ω

/--
[condFibre_eq_image_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma condFibre_eq_image_crossExt_eq
  {d n : ℕ} :
-- imply
  condFibre (innerEdgeFinset d n) (fun _ => false) = Finset.univ.image (crossExt d n) := by
-- proof
  apply StatMech.FK.condFibre_eq_image_crossExt d n

/--
[inducedBcZ_innerEdgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma inducedBcZ_innerEdgeFinset_eq
  {d n : ℕ}
  {p q : ℝ} :
-- imply
  inducedBcZ (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q (innerEdgeFinset d n) (fun _ => false) = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShift d n p q := by
-- proof
  apply StatMech.FK.inducedBcZ_innerEdgeFinset d n

/--
[condBcProb_crossExt_eq_wiredFkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma condBcProb_crossExt_eq_wiredFkProb_eq
  {d n : ℕ}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω) = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_crossExt_eq_wiredFkProb d n hp hp1 hq ω

/--
[boxBoundary_succ_iff_not_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma boxBoundary_succ_iff_not_inner_eq
  {d n : ℕ}
  {v : boxVerts d (n+1)} :
-- imply
  boxBoundary d (n+1) v ↔ ¬ IsInnerVert d n v := by
-- proof
  apply StatMech.FK.boxBoundary_succ_iff_not_inner d n v

/--
[isAnnulusWiring_boxBoundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma isAnnulusWiring_boxBoundary_succ_eq
  {d n : ℕ} :
-- imply
  IsAnnulusWiring d n (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) := by
-- proof
  apply StatMech.FK.isAnnulusWiring_boxBoundary_succ d n

/--
[openSub_sup_eq_crossWiredGraphAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma openSub_sup_eq_crossWiredGraphAdd_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))} :
-- imply
  openSub (boxGraph d (n+1)) (crossExt d n ω) ⊔ (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) = crossWiredGraphAdd d n ω D := by
-- proof
  apply StatMech.FK.openSub_sup_eq_crossWiredGraphAdd d n ω D

/--
[crossWiredGraphAdd_adj_inner_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_adj_inner_right_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {u w : boxVerts d (n+1)}
-- given
  (hD : IsAnnulusWiring d n D)
  (hu : IsInnerVert d n u)
  (h : (crossWiredGraphAdd d n ω D).Adj u w) :
-- imply
  IsInnerVert d n w := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_adj_inner_right d n ω hD hu h

/--
[crossWiredGraphAdd_not_adj_inner_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_not_adj_inner_annulus_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {u w : boxVerts d (n+1)}
-- given
  (hD : IsAnnulusWiring d n D)
  (hu : IsInnerVert d n u)
  (hw : ¬ IsInnerVert d n w) :
-- imply
  ¬ (crossWiredGraphAdd d n ω D).Adj u w := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_not_adj_inner_annulus d n ω hD hu hw

/--
[crossWiredGraphAdd_reachable_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_reachable_inner_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {u w : boxVerts d (n+1)}
-- given
  (hD : IsAnnulusWiring d n D)
  (hu : IsInnerVert d n u)
  (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
-- imply
  IsInnerVert d n w := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_reachable_inner d n ω hD hu h

/--
[crossWiredGraphAdd_reachable_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_reachable_annulus_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {u w : boxVerts d (n+1)}
-- given
  (hD : IsAnnulusWiring d n D)
  (hu : ¬ IsInnerVert d n u)
  (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
-- imply
  ¬ IsInnerVert d n w := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_reachable_annulus d n ω hD hu h

/--
[crossWiredGraphAdd_adj_boxVertIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_adj_boxVertIncl_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {x y : boxVerts d n}
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  (crossWiredGraphAdd d n ω D).Adj (boxVertIncl d n x) (boxVertIncl d n y) ↔ (innerWiredGraph d n ω).Adj x y := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_adj_boxVertIncl d n ω hD x y

/--
[crossWiredGraphAdd_adj_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossWiredGraphAdd_adj_annulus_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {a b : AnnulusVert d n} :
-- imply
  (crossWiredGraphAdd d n ω D).Adj a.1 b.1 ↔ (annulusSubgraph d n D).Adj a b := by
-- proof
  apply StatMech.FK.crossWiredGraphAdd_adj_annulus d n ω D a b

/--
[inner_reachable_of_crossWiredGraphAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma inner_reachable_of_crossWiredGraphAdd_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {x y : boxVerts d n}
-- given
  (hD : IsAnnulusWiring d n D)
  (h : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
-- imply
  (innerWiredGraph d n ω).Reachable x y := by
-- proof
  apply StatMech.FK.inner_reachable_of_crossWiredGraphAdd d n ω hD h

/--
[annulus_reachable_of_crossWiredGraphAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma annulus_reachable_of_crossWiredGraphAdd_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {a b : AnnulusVert d n}
-- given
  (hD : IsAnnulusWiring d n D)
  (h : (crossWiredGraphAdd d n ω D).Reachable a.1 b.1) :
-- imply
  (annulusSubgraph d n D).Reachable a b := by
-- proof
  apply StatMech.FK.annulus_reachable_of_crossWiredGraphAdd d n ω hD h

/--
[crossComponentEquivAddFun_inl_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivAddFun_inl_mk_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {x : boxVerts d n}
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  crossComponentEquivAddFun d n ω hD (Sum.inl ((innerWiredGraph d n ω).connectedComponentMk x)) = (crossWiredGraphAdd d n ω D).connectedComponentMk (boxVertIncl d n x) := by
-- proof
  apply StatMech.FK.crossComponentEquivAddFun_inl_mk d n ω hD x

/--
[crossComponentEquivAddFun_inr_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivAddFun_inr_mk_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  {a : AnnulusVert d n}
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  crossComponentEquivAddFun d n ω hD (Sum.inr ((annulusSubgraph d n D).connectedComponentMk a)) = (crossWiredGraphAdd d n ω D).connectedComponentMk a.1 := by
-- proof
  apply StatMech.FK.crossComponentEquivAddFun_inr_mk d n ω hD a

/--
[crossComponentEquivAddFun_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivAddFun_injective_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  Function.Injective (crossComponentEquivAddFun d n ω hD) := by
-- proof
  apply StatMech.FK.crossComponentEquivAddFun_injective d n ω hD

/--
[crossComponentEquivAddFun_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossComponentEquivAddFun_surjective_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  Function.Surjective (crossComponentEquivAddFun d n ω hD) := by
-- proof
  apply StatMech.FK.crossComponentEquivAddFun_surjective d n ω hD

/--
[numClustersBC_crossExt_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma numClustersBC_crossExt_add_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  [DecidableRel D.Adj]
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  numClustersBC (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) (crossExt d n ω) = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω + Nat.card (annulusSubgraph d n D).ConnectedComponent := by
-- proof
  apply StatMech.FK.numClustersBC_crossExt_add d n ω hD

/--
[crossShiftAdd_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma crossShiftAdd_pos_eq
  {d n : ℕ}
  {p q : ℝ}
  {D : SimpleGraph (boxVerts d (n+1))}
-- given
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 < crossShiftAdd d n p q D := by
-- proof
  apply StatMech.FK.crossShiftAdd_pos hp1 hq D

/--
[bcWeight_crossExt_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma bcWeight_crossExt_add_eq
  {d n : ℕ}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  [DecidableRel D.Adj]
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  bcWeight (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (crossExt d n ω) = wiredFkWeight (boxGraph d n) (boxBoundary d n) p q ω * crossShiftAdd d n p q D := by
-- proof
  apply StatMech.FK.bcWeight_crossExt_add d n ω hD

/--
[inducedBcZ_innerEdgeFinset_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma inducedBcZ_innerEdgeFinset_add_eq
  {d n : ℕ}
  {p q : ℝ}
  {D : SimpleGraph (boxVerts d (n+1))}
  [DecidableRel D.Adj]
-- given
  (hD : IsAnnulusWiring d n D) :
-- imply
  inducedBcZ (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (innerEdgeFinset d n) (fun _ => false) = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShiftAdd d n p q D := by
-- proof
  apply StatMech.FK.inducedBcZ_innerEdgeFinset_add d n hD

/--
[condBcProb_crossExt_eq_wiredFkProb_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean)
-/
@[path]
private lemma condBcProb_crossExt_eq_wiredFkProb_add_eq
  {d n : ℕ}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))}
  {D : SimpleGraph (boxVerts d (n+1))}
  [DecidableRel D.Adj]
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hD : IsAnnulusWiring d n D) :
-- imply
  condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω) = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_crossExt_eq_wiredFkProb_add d n hp hp1 hq ω hD


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[ocs_orderedEdges_firstIn_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_orderedEdges_firstIn_le_eq
  {d : ℕ}
  {d n : ℕ}
  {S : Finset (Site d)} :
-- imply
  ((boxSV_edgeF d n).filter (fun p => p.1 ∈ S)).card ≤ S.card * (2 * d) := by
-- proof
  apply StatMech.FK.ocs_orderedEdges_firstIn_le d n S

/--
[ocs_orderedEdges_secondIn_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_orderedEdges_secondIn_le_eq
  {d : ℕ}
  {d n : ℕ}
  {S : Finset (Site d)} :
-- imply
  ((boxSV_edgeF d n).filter (fun p => p.2 ∈ S)).card ≤ S.card * (2 * d) := by
-- proof
  apply StatMech.FK.ocs_orderedEdges_secondIn_le d n S

/--
[ocs_edgeF_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_edgeF_mono_eq
  {d : ℕ}
  {d m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  boxSV_edgeF d m ⊆ boxSV_edgeF d n := by
-- proof
  apply StatMech.FK.ocs_edgeF_mono h

/--
[ocs_edgeCard_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_edgeCard_sub_le_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  boxSV_edgeCard d n - boxSV_edgeCard d m ≤ 4 * d * (boxSV_boxF d n \ boxSV_boxF d m).card := by
-- proof
  apply StatMech.FK.ocs_edgeCard_sub_le d h

/--
[ocs_sqrt_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_sqrt_tendsto_atTop_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => Nat.sqrt n) atTop atTop := by
-- proof
  apply StatMech.FK.ocs_sqrt_tendsto_atTop

/--
[ocs_inv_sqrt_to_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_inv_sqrt_to_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_inv_sqrt_to_zero

/--
[ocs_sqrt_div_to_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_sqrt_div_to_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_sqrt_div_to_zero

/--
[ocs_edgeCard_shell_fraction_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_edgeCard_shell_fraction_le_eq
  {d : ℕ}
  {d : ℕ}
  {n m : ℕ}
-- given
  (hd : 1 ≤ d)
  (hn : 1 ≤ n)
  (hmn : m ≤ n) :
-- imply
  ((boxSV_edgeCard d n - boxSV_edgeCard d m : ℕ) : ℝ) / (boxSV_edgeCard d n) ≤ 4 * (d : ℝ) ^ 2 * (((n - m : ℕ) : ℝ) / n) := by
-- proof
  apply StatMech.FK.ocs_edgeCard_shell_fraction_le d hd n m hn hmn

/--
[ocs_gap_sub_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_gap_sub_tendsto_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n => ((n - (n - Nat.sqrt n) : ℕ) : ℝ) / n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_gap_sub_tendsto_zero

/--
[ocs_gap_sub_one_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_gap_sub_one_tendsto_zero_eq
  {d : ℕ} :
-- imply
  Tendsto (fun n => ((n - (n - Nat.sqrt n - 1) : ℕ) : ℝ) / n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_gap_sub_one_tendsto_zero

/--
[ocs_edgeFinset_shell_fraction_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_edgeFinset_shell_fraction_tendsto_zero_eq
  {d : ℕ}
  {d : ℕ}
  {m : ℕ → ℕ}
-- given
  (hd : 1 ≤ d)
  (hm : ∀ n, m n ≤ n)
  (hgap : Tendsto (fun n => ((n - m n : ℕ) : ℝ) / n) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (boxGraph d (m n)).edgeFinset.card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_edgeFinset_shell_fraction_tendsto_zero d hd m hm hgap

/--
[ocs_innerEdge_recentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_innerEdge_recentre_eq
  {d : ℕ}
  {d R n md : ℕ}
  {u v : boxVerts d md}
-- given
  (hmn : md ≤ n)
  (hsub : fvs_transBox d R ((u : Site d)) ⊆ box d n)
  (c0 : (0 : Site d) ∈ box d R)
  (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
-- imply
  ocd_innerEdge (flc_incl hsub) (Sym2.map (fvs_transEquiv d R (u : Site d)) (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)))) = innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d md)) := by
-- proof
  apply StatMech.FK.ocs_innerEdge_recentre d R n md hmn u v hsub c0 cw

/--
[ocs_free_offCentre_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_free_offCentre_lower_eq
  {d : ℕ}
  {d R n : ℕ}
  {u v : boxVerts d (n - R)}
  {p : ℝ}
-- given
  (hRn : R ≤ n)
  (hmn : n - R ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (c0 : (0 : Site d) ∈ box d R)
  (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
-- imply
  edgeMargProb (fkProb (boxGraph d R) p 2) (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) ≤ edgeMargProb (fkProb (boxGraph d n) p 2) (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R)))) := by
-- proof
  apply StatMech.FK.ocs_free_offCentre_lower d R n hRn hmn u v hp hp1 c0 cw

/--
[ocs_wired_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wired_margin_eq
  {d : ℕ}
  {d R n : ℕ}
  {a : Site d}
-- given
  (ha : a ∈ box d (n - R - 1))
  (hRn : R + 1 ≤ n)
  (hsub : fvs_transBox d R a ⊆ box d n)
  (x : {y : Site d // y ∈ fvs_transBox d R a}) :
-- imply
  ¬ boxBoundary d n (flc_incl hsub x) := by
-- proof
  apply StatMech.FK.ocs_wired_margin d R n a ha hRn hsub x

/--
[ocs_wired_offCentre_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wired_offCentre_upper_eq
  {d : ℕ}
  {d R n : ℕ}
  {u v : boxVerts d (n - R - 1)}
  {p : ℝ}
-- given
  (hR : 1 ≤ R)
  (hRn1 : R + 1 ≤ n)
  (hmn : n - R - 1 ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (c0 : (0 : Site d) ∈ box d R)
  (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R - 1)))) ≤ edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p 2) (s((⟨(0 : Site d), c0⟩ : boxVerts d R), (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) := by
-- proof
  apply StatMech.FK.ocs_wired_offCentre_upper d R n hR hRn1 hmn u v hp hp1 c0 cw

/--
[ocs_zero_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_zero_mem_box_eq
  {d : ℕ}
  {d R : ℕ} :
-- imply
  (0 : Site d) ∈ box d R := by
-- proof
  apply StatMech.FK.ocs_zero_mem_box d R

/--
[ocs_candMap_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_candMap_mem_box_eq
  {d : ℕ}
  {d R : ℕ}
  {p : Fin d × Bool}
-- given
  (hR : 1 ≤ R) :
-- imply
  candMap d (0 : Site d) p ∈ box d R := by
-- proof
  apply StatMech.FK.ocs_candMap_mem_box d R hR p

/--
[ocs_edge_dir_candMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_edge_dir_candMap_eq
  {d : ℕ}
  {d m : ℕ}
  {u v : boxVerts d m}
-- given
  (hadj : (boxGraph d m).Adj u v) :
-- imply
  ∃ p : Fin d × Bool, (v : Site d) - (u : Site d) = candMap d (0 : Site d) p := by
-- proof
  apply StatMech.FK.ocs_edge_dir_candMap d m u v hadj

/--
[ocs_unitEdge_eq_innerEdgeLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_unitEdge_eq_innerEdgeLE_eq
  {d : ℕ}
  {d r : ℕ}
  {p : Fin d × Bool}
-- given
  (hr : 1 ≤ r) :
-- imply
  ocs_unitEdge d r hr p = innerEdgeLE d hr (ocs_unitEdge d 1 (le_refl 1) p) := by
-- proof
  apply StatMech.FK.ocs_unitEdge_eq_innerEdgeLE d r hr p

/--
[ocs_unitEdge1_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_unitEdge1_mem_edgeFinset_eq
  {d : ℕ}
  {d : ℕ}
  {p : Fin d × Bool} :
-- imply
  ocs_unitEdge d 1 (le_refl 1) p ∈ (boxGraph d 1).edgeFinset := by
-- proof
  apply StatMech.FK.ocs_unitEdge1_mem_edgeFinset d p

/--
[ocs_unitEdge_marg_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_unitEdge_marg_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {p : Fin d × Bool}
  {pr : ℝ}
-- given
  (hp : 0 < pr)
  (hp1 : pr < 1) :
-- imply
  Tendsto (fun n => if hR : 1 ≤ Nat.sqrt n then edgeMargProb (fkProb (boxGraph d (Nat.sqrt n)) pr 2) (ocs_unitEdge d (Nat.sqrt n) hR p) else (0 : ℝ)) atTop (𝓝 (freeEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
-- proof
  apply StatMech.FK.ocs_unitEdge_marg_tendsto d p hp hp1

/--
[ocs_freeDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_freeDelta_nonneg_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ ocs_freeDelta N e' t n := by
-- proof
  apply StatMech.FK.ocs_freeDelta_nonneg N e' t n

/--
[ocs_perDir_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_perDir_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {p : Fin d × Bool}
-- given
  (hres : ocs_FreeRotationResidue (d := d) N e' t) :
-- imply
  Tendsto (fun n => |freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_unitMarg d n p t|) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_perDir_tendsto_zero N e' t hres p

/--
[ocs_freeDelta_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_freeDelta_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hres : ocs_FreeRotationResidue (d := d) N e' t) :
-- imply
  Tendsto (fun n => ocs_freeDelta N e' t n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_freeDelta_tendsto_zero N e' t hres

/--
[ocs_innerEdgeLE_mem_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_innerEdgeLE_mem_edgeFinset_eq
  {d : ℕ}
  {d : ℕ}
  {m n : ℕ}
  {eb : Sym2 (boxVerts d m)}
-- given
  (h : m ≤ n)
  (heb : eb ∈ (boxGraph d m).edgeFinset) :
-- imply
  innerEdgeLE d h eb ∈ (boxGraph d n).edgeFinset := by
-- proof
  apply StatMech.FK.ocs_innerEdgeLE_mem_edgeFinset d h eb heb

/--
[ocs_free_bulk_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_free_bulk_lower_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {n : ℕ}
  {u v : boxVerts d (n - Nat.sqrt n)}
-- given
  (hn : 1 ≤ n)
  (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) - ocs_freeDelta N e' t n ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
-- proof
  apply StatMech.FK.ocs_free_bulk_lower N e' t n hn u v hadj

/--
[ocs_freeOffCentreSandwich_of_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_freeOffCentreSandwich_of_rotation_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t) :
-- imply
  bdp_FreeOffCentreSandwich (d := d) N := by
-- proof
  apply StatMech.FK.ocs_freeOffCentreSandwich_of_rotation hd N hres

/--
[ocs_unitEdge_wired_marg_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_unitEdge_wired_marg_tendsto_eq
  {d : ℕ}
  {d : ℕ}
  {p : Fin d × Bool}
  {pr : ℝ}
-- given
  (hp : 0 < pr)
  (hp1 : pr < 1) :
-- imply
  Tendsto (fun n => if hR : 1 ≤ Nat.sqrt n then edgeMargProb (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n)) pr 2) (ocs_unitEdge d (Nat.sqrt n) hR p) else (0 : ℝ)) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) p)) pr)) := by
-- proof
  apply StatMech.FK.ocs_unitEdge_wired_marg_tendsto d p hp hp1

/--
[ocs_wiredDelta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wiredDelta_nonneg_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ ocs_wiredDelta N e' t n := by
-- proof
  apply StatMech.FK.ocs_wiredDelta_nonneg N e' t n

/--
[ocs_wired_perDir_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wired_perDir_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {p : Fin d × Bool}
-- given
  (hres : ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  Tendsto (fun n => |ocs_unitWiredMarg d n p t - wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t)|) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_wired_perDir_tendsto_zero N e' t hres p

/--
[ocs_wiredDelta_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wiredDelta_tendsto_zero_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hres : ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  Tendsto (fun n => ocs_wiredDelta N e' t n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.ocs_wiredDelta_tendsto_zero N e' t hres

/--
[ocs_wired_bulk_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wired_bulk_upper_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
  {n : ℕ}
  {u v : boxVerts d (n - Nat.sqrt n - 1)}
-- given
  (hn : 2 ≤ n)
  (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))) (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1)))) ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) + ocs_wiredDelta N e' t n := by
-- proof
  apply StatMech.FK.ocs_wired_bulk_upper N e' t n hn u v hadj

/--
[ocs_wiredOffCentreSandwich_of_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_wiredOffCentreSandwich_of_rotation_eq
  {d : ℕ}
  {N : ℕ}
-- given
  (hd : 1 ≤ d)
  (hres : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  bdp_WiredOffCentreSandwich (d := d) N := by
-- proof
  apply StatMech.FK.ocs_wiredOffCentreSandwich_of_rotation hd N hres

/--
[ocs_fk_uniqueness_of_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreSandwichProof.lean)
-/
@[path]
private lemma ocs_fk_uniqueness_of_rotation_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hfreeRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
  (hwiredRot : ∀ (e' : Sym2 (boxVerts d N)) (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.ocs_fk_uniqueness_of_rotation hd N eb hEbox hg hboxfree hfreeRot hwiredRot


-- created on 2026-10-23

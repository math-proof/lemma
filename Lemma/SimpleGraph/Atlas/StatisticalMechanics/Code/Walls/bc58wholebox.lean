import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc58_mem_boxInternalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_mem_boxInternalEdges_eq
  {d : ℕ}
  {d k : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d k)
  (hy : y ∈ box d k)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  s(x, y) ∈ bc58_boxInternalEdges d k := by
-- proof
  apply StatMech.Walls.bc58_mem_boxInternalEdges hx hy hadj

/--
[bc58_boxOpen_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_boxOpen_edge_open_eq
  {d : ℕ}
  {d k : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hx : x ∈ box d k)
  (hy : y ∈ box d k)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  IsOpenEdge d (bc58_boxOpen d k ω) x y := by
-- proof
  apply StatMech.Walls.bc58_boxOpen_edge_open hx hy hadj ω

/--
[bc58_boxOpen_adj_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_boxOpen_adj_connected_eq
  {d : ℕ}
  {d k : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hx : x ∈ box d k)
  (hy : y ∈ box d k)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  Connected d (bc58_boxOpen d k ω) x y := by
-- proof
  apply StatMech.Walls.bc58_boxOpen_adj_connected hx hy hadj ω

/--
[bc58_boxOpen_removeSite_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_boxOpen_removeSite_edge_open_eq
  {d : ℕ}
  {d k : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hx : x ∈ box d k)
  (hy : y ∈ box d k)
  (hadj : (hypercubicLattice d).Adj x y)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  IsOpenEdge d (removeSite 0 (bc58_boxOpen d k ω)) x y := by
-- proof
  apply StatMech.Walls.bc58_boxOpen_removeSite_edge_open hx hy hadj h0 ω

/--
[bc58_boxOpen_removeSite_adj_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_boxOpen_removeSite_adj_connected_eq
  {d : ℕ}
  {d k : ℕ}
  {x y : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hx : x ∈ box d k)
  (hy : y ∈ box d k)
  (hadj : (hypercubicLattice d).Adj x y)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  Connected d (removeSite 0 (bc58_boxOpen d k ω)) x y := by
-- proof
  apply StatMech.Walls.bc58_boxOpen_removeSite_adj_connected hx hy hadj h0 ω

/--
[bc58_p_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_fst_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  (bc58_p a b) 0 = a := by
-- proof
  apply StatMech.Walls.bc58_p_fst a b

/--
[bc58_p_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_snd_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  (bc58_p a b) 1 = b := by
-- proof
  apply StatMech.Walls.bc58_p_snd a b

/--
[bc58_p_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_mem_box_eq
  {d : ℕ}
  {k : ℕ}
  {a b : ℤ}
-- given
  (ha : a.natAbs ≤ k)
  (hb : b.natAbs ≤ k) :
-- imply
  bc58_p a b ∈ box 2 k := by
-- proof
  apply StatMech.Walls.bc58_p_mem_box ha hb

/--
[bc58_p_adj_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_adj_horiz_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p (a + 1) b) := by
-- proof
  apply StatMech.Walls.bc58_p_adj_horiz a b

/--
[bc58_p_adj_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_adj_vert_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p a (b + 1)) := by
-- proof
  apply StatMech.Walls.bc58_p_adj_vert a b

/--
[bc58_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_origin_eq_eq
  {d : ℕ} :
-- imply
  (0 : Site 2) = bc58_p 0 0 := by
-- proof
  apply StatMech.Walls.bc58_origin_eq

/--
[bc58_p_eq_origin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_p_eq_origin_iff_eq
  {d : ℕ}
  {a b : ℤ} :
-- imply
  bc58_p a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
-- proof
  apply StatMech.Walls.bc58_p_eq_origin_iff

/--
[bc58_origin_notMem_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_origin_notMem_edge_eq
  {d : ℕ}
  {a b c e : ℤ}
-- given
  (h0 : ¬ (a = 0 ∧ b = 0))
  (h1 : ¬ (c = 0 ∧ e = 0)) :
-- imply
  (0 : Site 2) ∉ s(bc58_p a b, bc58_p c e) := by
-- proof
  apply StatMech.Walls.bc58_origin_notMem_edge h0 h1

/--
[bc58_reconnect_around_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_reconnect_around_origin_eq
  {d : ℕ}
  {k : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hk : 1 ≤ k) :
-- imply
  Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0) := by
-- proof
  apply StatMech.Walls.bc58_reconnect_around_origin hk ω

/--
[bc58_disjointRouting_of_originTrifModification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_disjointRouting_of_originTrifModification_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc58_OriginTrifModification d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Walls.bc58_disjointRouting_of_originTrifModification h

/--
[bc58_hroute_of_originTrifModification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_hroute_of_originTrifModification_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc58_hroute_of_originTrifModification μ hfe hmod

/--
[bc58_burton_keane_bernoulli_of_originTrifModification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_burton_keane_bernoulli_of_originTrifModification_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hmod : ∀ n : ℕ, bc58_OriginTrifModification d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc58_burton_keane_bernoulli_of_originTrifModification hd p hp1 hp0 hmod

/--
[bc58_origin_nbr_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_origin_nbr_cases_eq
  {d : ℕ}
  {a : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj 0 a) :
-- imply
  a = bc58_p 1 0 ∨ a = bc58_p (-1) 0 ∨ a = bc58_p 0 1 ∨ a = bc58_p 0 (-1) := by
-- proof
  apply StatMech.Walls.bc58_origin_nbr_cases hadj

/--
[bc58_origin_nbr_connected_to_e](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_origin_nbr_connected_to_e_eq
  {d : ℕ}
  {k : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
-- given
  (hk : 1 ≤ k)
  (hadj : (hypercubicLattice 2).Adj 0 a) :
-- imply
  Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a (bc58_p 1 0) := by
-- proof
  apply StatMech.Walls.bc58_origin_nbr_connected_to_e hk ω hadj

/--
[bc58_origin_nbrs_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_origin_nbrs_connected_eq
  {d : ℕ}
  {k : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : Site 2}
-- given
  (hk : 1 ≤ k)
  (ha : (hypercubicLattice 2).Adj 0 a)
  (hb : (hypercubicLattice 2).Adj 0 b) :
-- imply
  Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) a b := by
-- proof
  apply StatMech.Walls.bc58_origin_nbrs_connected hk ω ha hb

/--
[bc58_boxOpen_not_classicalTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_boxOpen_not_classicalTrif_eq
  {d : ℕ}
  {k : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hk : 1 ≤ k) :
-- imply
  ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0 := by
-- proof
  apply StatMech.Walls.bc58_boxOpen_not_classicalTrif hk ω

/--
[bc58_wholeBoxG_not_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_wholeBoxG_not_witness_eq
  {d : ℕ}
  {k : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hk : 1 ≤ k) :
-- imply
  ¬ bc47_IsClassicalTrifurcation (forceOpenFinset (bc58_boxInternalEdges 2 k) ω) 0 := by
-- proof
  apply StatMech.Walls.bc58_wholeBoxG_not_witness hk ω

/--
[bc58_evenLines_boxOpen_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_evenLines_boxOpen_reconnect_eq
  {d : ℕ}
  {k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k bc57_evenLines) 0 := by
-- proof
  apply StatMech.Walls.bc58_evenLines_boxOpen_reconnect hk

/--
[bc58_threeMeet_evenLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_threeMeet_evenLines_eq
  {d : ℕ} :
-- imply
  bc57_evenLines ∈ threeMeetBox 2 6 := by
-- proof
  apply StatMech.Walls.bc58_threeMeet_evenLines

/--
[bc58_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean)
-/
@[path]
private lemma bc58_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  ((∀ n : ℕ, bc58_OriginTrifModification d n) → (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)), Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0)) ∧ (∀ {k : ℕ}, 1 ≤ k → ∀ ω : ConfigSpace (Sym2 (Site 2)), ¬ bc47_IsClassicalTrifurcation (bc58_boxOpen 2 k ω) 0) ∧ (bc57_evenLines ∈ threeMeetBox 2 6) := by
-- proof
  apply StatMech.Walls.bc58_status hd p hp1 hp0


-- created on 2026-10-23

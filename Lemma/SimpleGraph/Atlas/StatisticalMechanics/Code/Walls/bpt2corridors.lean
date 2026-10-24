import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bpt2corridors
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bpt2_closeI_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_closeI_le_eq
  {I : Finset (Sym2 (Site 2))}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  bpt2_closeI I ω ≤ ω := by
-- proof
  apply StatMech.Walls.bpt2_closeI_le I ω

/--
[bpt2_removeSite_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_removeSite_mono_eq
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (h : ω ≤ ω') :
-- imply
  removeSite z ω ≤ removeSite z ω' := by
-- proof
  apply StatMech.Walls.bpt2_removeSite_mono h z

/--
[bpt2_closeI_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_closeI_forceOpen_eq
  {I : Finset (Sym2 (Site 2))}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  bpt2_closeI I (forceOpenFinset I ω) = bpt2_closeI I ω := by
-- proof
  apply StatMech.Walls.bpt2_closeI_forceOpen I ω

/--
[bpt2_openEdge_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_openEdge_data_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 (removeSite 0 ω) u v) :
-- imply
  (0 : Site 2) ∉ s(u, v) ∧ (hypercubicLattice 2).Adj u v ∧ ω s(u, v) = true := by
-- proof
  apply StatMech.Walls.bpt2_openEdge_data ω h

/--
[bpt2_closed_combined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_closed_combined_eq
  {I : Finset (Sym2 (Site 2))}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
-- given
  (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
  (hSclosed : ∀ u v : Site 2, u ∈ S → IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
-- imply
  ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S := by
-- proof
  apply StatMech.Walls.bpt2_closed_combined I ω hIresp hSclosed

/--
[bpt2_walk_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_walk_invariant_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (openSubgraph 2 (removeSite 0 ω)).Walk x y}
-- given
  (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S)
  (hx : x ∈ S) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Walls.bpt2_walk_invariant ω hclosed w hx

/--
[bpt2_cluster_confined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_cluster_confined_eq
  {I : Finset (Sym2 (Site 2))}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a : Site 2}
  {S : Set (Site 2)}
-- given
  (ha : a ∈ S)
  (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
  (hSclosed : ∀ u v : Site 2, u ∈ S → IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
-- imply
  cluster 2 (removeSite 0 ω) a ⊆ S := by
-- proof
  apply StatMech.Walls.bpt2_cluster_confined I ω ha hIresp hSclosed

/--
[bpt2_removeSite_closeI_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_removeSite_closeI_congr_eq
  {I : Finset (Sym2 (Site 2))}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (hag : agreeOn ((↑I : Set (Sym2 (Site 2)))ᶜ) ω ω') :
-- imply
  removeSite 0 (bpt2_closeI I ω) = removeSite 0 (bpt2_closeI I ω') := by
-- proof
  apply StatMech.Walls.bpt2_removeSite_closeI_congr I hag

/--
[bpt2_Ext_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_Ext_dependsOn_eq
  {I : Finset (Sym2 (Site 2))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2} :
-- imply
  DependsOn (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) ((↑I : Set (Sym2 (Site 2)))ᶜ) := by
-- proof
  apply StatMech.Walls.bpt2_Ext_dependsOn I a₁ a₂ a₃ x₁ x₂ x₃

/--
[bpt2_hgeo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_hgeo_eq
  {I : Finset (Sym2 (Site 2))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}
  {η₀ : ConfigSpace ↥I}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃)
  (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)), Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧ Connected 2 (removeSite 0 ω) a₃ x₃) :
-- imply
  cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃ ⊆ NeighborTrifPrecursor 2 a₁ a₂ a₃ := by
-- proof
  apply StatMech.Walls.bpt2_hgeo I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr

/--
[bpt2_precursorPos_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_precursorPos_of_residues_eq
  {I : Finset (Sym2 (Site 2))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}
  {η₀ : ConfigSpace ↥I}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hplt : p < 1)
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃)
  (hcorr : ∀ ω ∈ cylinder I ({η₀} : Set (ConfigSpace ↥I)), Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧ Connected 2 (removeSite 0 ω) a₃ x₃)
  (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I)) ∩ bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃) = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (cylinder I ({η₀} : Set (ConfigSpace ↥I))) * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃))
  (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (bpt2_Ext I a₁ a₂ a₃ x₁ x₂ x₃)) :
-- imply
  0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (NeighborTrifPrecursor 2 a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bpt2_precursorPos_of_residues p hp1 hp0 hplt I a₁ a₂ a₃ x₁ x₂ x₃ η₀ hne hadj hcorr hindep hXpos

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq :
-- imply
  bmf_a₁ ∈ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_x_eq :
-- imply
  bmf_b₁ ∈ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_x

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_2 :
-- imply
  bmf_a₂ ∈ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_x_eq_2 :
-- imply
  bmf_b₂ ∈ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_x

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_3 :
-- imply
  bmf_a₃ ∈ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_x_eq_3 :
-- imply
  bmf_b₃ ∈ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_x

/--
[bpt2_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_R_eq
  {v : Site 2}
-- given
  (h : v ∈ bmf_R₁) :
-- imply
  v ∈ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_R h

/--
[bpt2_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_R_eq_2
  {v : Site 2}
-- given
  (h : v ∈ bmf_R₂) :
-- imply
  v ∈ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_R h

/--
[bpt2_R](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_R_eq_3
  {v : Site 2}
-- given
  (h : v ∈ bmf_R₃) :
-- imply
  v ∈ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_R h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₁) :
-- imply
  v ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_2
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₁) :
-- imply
  v ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_3
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₂) :
-- imply
  v ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_4
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₂) :
-- imply
  v ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_5
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₃) :
-- imply
  v ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_6
  {v : Site 2}
-- given
  (h : v ∈ bpt2_S₃) :
-- imply
  v ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_S h

/--
[bpt2_disjoint_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_disjoint_S_eq :
-- imply
  Disjoint bpt2_S₁ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_disjoint_S

/--
[bpt2_disjoint_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_disjoint_S_eq_2 :
-- imply
  Disjoint bpt2_S₁ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_disjoint_S

/--
[bpt2_disjoint_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_disjoint_S_eq_3 :
-- imply
  Disjoint bpt2_S₂ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_disjoint_S

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_4 :
-- imply
  bmf_a₂ ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq :
-- imply
  bmf_b₂ ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_5 :
-- imply
  bmf_a₃ ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq_2 :
-- imply
  bmf_b₃ ∉ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_6 :
-- imply
  bmf_a₁ ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq_3 :
-- imply
  bmf_b₁ ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_7 :
-- imply
  bmf_a₃ ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq_4 :
-- imply
  bmf_b₃ ∉ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_8 :
-- imply
  bmf_a₁ ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq_5 :
-- imply
  bmf_b₁ ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_9 :
-- imply
  bmf_a₂ ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_b](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_b_eq_6 :
-- imply
  bmf_b₂ ∉ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_b

/--
[bpt2_I_respects_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_I_respects_S_eq
  {u v : Site 2}
-- given
  (hmem : s(u, v) ∈ bmf_I)
  (hu : u ∈ bpt2_S₁) :
-- imply
  v ∈ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_I_respects_S u v hmem hu

/--
[bpt2_I_respects_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_I_respects_S_eq_2
  {u v : Site 2}
-- given
  (hmem : s(u, v) ∈ bmf_I)
  (hu : u ∈ bpt2_S₂) :
-- imply
  v ∈ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_I_respects_S u v hmem hu

/--
[bpt2_I_respects_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_I_respects_S_eq_3
  {u v : Site 2}
-- given
  (hmem : s(u, v) ∈ bmf_I)
  (hu : u ∈ bpt2_S₃) :
-- imply
  v ∈ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_I_respects_S u v hmem hu

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_10 :
-- imply
  bmf_a₁ ∉ bmf_R₁ ∧ bmf_a₁ ∉ bmf_R₂ ∧ bmf_a₁ ∉ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_11 :
-- imply
  bmf_a₂ ∉ bmf_R₁ ∧ bmf_a₂ ∉ bmf_R₂ ∧ bmf_a₂ ∉ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_a](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_a_eq_12 :
-- imply
  bmf_a₃ ∉ bmf_R₁ ∧ bmf_a₃ ∉ bmf_R₂ ∧ bmf_a₃ ∉ bmf_R₃ := by
-- proof
  apply StatMech.Walls.bpt2_a

/--
[bpt2_notOnRay_of_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_notOnRay_of_endpoint_eq
  {e : Sym2 (Site 2)}
  {a : Site 2}
-- given
  (hae : a ∈ e)
  (hR : a ∉ bmf_R₁ ∧ a ∉ bmf_R₂ ∧ a ∉ bmf_R₃) :
-- imply
  ¬ bmf_OnRay e := by
-- proof
  apply StatMech.Walls.bpt2_notOnRay_of_endpoint hae hR

/--
[bpt2_closeI_omegaTri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_closeI_omegaTri_eq :
-- imply
  bpt2_closeI bmf_I bmf_omegaTri = bmf_omegaTri := by
-- proof
  apply StatMech.Walls.bpt2_closeI_omegaTri

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_7
  {u v : Site 2}
-- given
  (hu : u ∈ bpt2_S₁)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) :
-- imply
  v ∈ bpt2_S₁ := by
-- proof
  apply StatMech.Walls.bpt2_S u v hu hop

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_8
  {u v : Site 2}
-- given
  (hu : u ∈ bpt2_S₂)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) :
-- imply
  v ∈ bpt2_S₂ := by
-- proof
  apply StatMech.Walls.bpt2_S u v hu hop

/--
[bpt2_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_S_eq_9
  {u v : Site 2}
-- given
  (hu : u ∈ bpt2_S₃)
  (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) :
-- imply
  v ∈ bpt2_S₃ := by
-- proof
  apply StatMech.Walls.bpt2_S u v hu hop

/--
[bpt2_removeSite_closeI_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_removeSite_closeI_omega_eq :
-- imply
  removeSite 0 (bpt2_closeI bmf_I bpt2_omega) = removeSite 0 bmf_omegaTri := by
-- proof
  apply StatMech.Walls.bpt2_removeSite_closeI_omega

/--
[bpt2_omega_mem_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_omega_mem_cylinder_eq :
-- imply
  bpt2_omega ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) := by
-- proof
  apply StatMech.Walls.bpt2_omega_mem_cylinder

/--
[bpt2_omega_mem_Ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_omega_mem_Ext_eq :
-- imply
  bpt2_omega ∈ bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃ := by
-- proof
  apply StatMech.Walls.bpt2_omega_mem_Ext

/--
[bpt2_omega_mem_precursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_omega_mem_precursor_eq :
-- imply
  bpt2_omega ∈ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ := by
-- proof
  apply StatMech.Walls.bpt2_omega_mem_precursor

/--
[bpt2_Ext_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean)
-/
@[path]
private lemma bpt2_Ext_nonempty_eq :
-- imply
  (bpt2_Ext bmf_I bmf_a₁ bmf_a₂ bmf_a₃ bmf_b₁ bmf_b₂ bmf_b₃).Nonempty := by
-- proof
  apply StatMech.Walls.bpt2_Ext_nonempty


-- created on 2026-10-23

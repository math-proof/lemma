import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[spc_survivor_has_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_survivor_has_neighbor_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {B : Set V}
  {v : V}
-- given
  (h : spc_OnBPath T B v) :
-- imply
  ∃ w, T.Adj v w ∧ spc_OnBPath T B w := by
-- proof
  apply StatMech.Percolation.spc_survivor_has_neighbor T B v h

/--
[spc_interior_two_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_interior_two_neighbors_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {B : Set V}
  {v : V}
-- given
  (hv : spc_OnBPath T B v)
  (hvB : v ∉ B) :
-- imply
  ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧ T.Adj v w₁ ∧ T.Adj v w₂ ∧ spc_OnBPath T B w₁ ∧ spc_OnBPath T B w₂ := by
-- proof
  apply StatMech.Percolation.spc_interior_two_neighbors T B v hv hvB

/--
[spc_deg_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_deg_ge_one_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {F : SimpleGraph W}
  [DecidableRel F.Adj]
  {v w : W}
-- given
  (h : F.Adj v w) :
-- imply
  1 ≤ F.degree v := by
-- proof
  apply StatMech.Percolation.spc_deg_ge_one F v w h

/--
[spc_deg_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_deg_ge_two_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {F : SimpleGraph W}
  [DecidableRel F.Adj]
  {v w₁ w₂ : W}
-- given
  (hne : w₁ ≠ w₂)
  (h0 : F.Adj v w₁)
  (h1 : F.Adj v w₂) :
-- imply
  2 ≤ F.degree v := by
-- proof
  apply StatMech.Percolation.spc_deg_ge_two F v w₁ w₂ hne h0 h1

/--
[spc_deg_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_deg_ge_three_eq
  {d : ℕ}
  [Fintype W]
  [DecidableEq W]
  {F : SimpleGraph W}
  [DecidableRel F.Adj]
  {v w₁ w₂ w₃ : W}
-- given
  (h12 : w₁ ≠ w₂)
  (h13 : w₁ ≠ w₃)
  (h23 : w₂ ≠ w₃)
  (h0 : F.Adj v w₁)
  (h1 : F.Adj v w₂)
  (h2 : F.Adj v w₃) :
-- imply
  3 ≤ F.degree v := by
-- proof
  apply StatMech.Percolation.spc_deg_ge_three F v w₁ w₂ w₃ h12 h13 h23 h0 h1 h2

/--
[spc_map_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_map_acyclic_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {f : V ↪ V'}
-- given
  (hac : G.IsAcyclic) :
-- imply
  (SimpleGraph.map f G).IsAcyclic := by
-- proof
  apply StatMech.Percolation.spc_map_acyclic hac f

/--
[spc_peeledBoxForest_of_spanForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_peeledBoxForest_of_spanForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : spc_SpanForestArms ω n) :
-- imply
  osf_PeeledBoxForest ω n := by
-- proof
  apply StatMech.Percolation.spc_peeledBoxForest_of_spanForestArms ω n h

/--
[spc_boxOpenForest_of_spanForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_boxOpenForest_of_spanForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : spc_SpanForestArms ω n) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Percolation.spc_boxOpenForest_of_spanForestArms ω n h

/--
[spc_Tcount_le_boundary_of_spanForestArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_Tcount_le_boundary_of_spanForestArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : spc_SpanForestArms ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.spc_Tcount_le_boundary_of_spanForestArms ω n h

/--
[spc_spanForestArms_of_boundary_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_spanForestArms_of_boundary_edge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {b₁ b₂ : Site d}
-- given
  (hb1 : b₁ ∈ vertexBoundary d n)
  (hb2 : b₂ ∈ vertexBoundary d n)
  (hbne : b₁ ≠ b₂)
  (hopen : (openSubgraph d ω).Adj b₁ b₂)
  (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  spc_SpanForestArms ω n := by
-- proof
  apply StatMech.Percolation.spc_spanForestArms_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif

/--
[spc_spanForestArms_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SecondPeelingClose.lean)
-/
@[path]
private lemma spc_spanForestArms_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  spc_SpanForestArms ω n := by
-- proof
  apply StatMech.Percolation.spc_spanForestArms_star ω n a hsingle hadj habdry hxne hainj hsep


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[reachable_induce_of_walk_in_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma reachable_induce_of_walk_in_support_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {f g : Site 2}
  {p : (faceBoundaryGraph K).Walk f g}
-- given
  (hsub : ∀ v ∈ p.support, v ∈ T)
  (hf : f ∈ T) :
-- imply
  ((faceBoundaryGraph K).induce (T : Set (Site 2))).Reachable ⟨f, hf⟩ ⟨g, hsub g p.end_mem_support⟩ := by
-- proof
  apply StatMech.Lattice.reachable_induce_of_walk_in_support p hsub hf

/--
[faceBoundaryConnected_of_walks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma faceBoundaryConnected_of_walks_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
-- given
  (hne : T.Nonempty)
  (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g, ∀ v ∈ p.support, v ∈ T) :
-- imply
  FaceBoundaryConnected K T := by
-- proof
  apply StatMech.Lattice.faceBoundaryConnected_of_walks hne hwalk

/--
[mem_singletonOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_singletonOrigin_eq
  {p q : ℤ} :
-- imply
  (![p, q] : Site 2) ∈ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ↔ p = 0 ∧ q = 0 := by
-- proof
  apply StatMech.Lattice.mem_singletonOrigin p q

/--
[singleton_adj_00_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singleton_adj_00_L_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj ![(0:ℤ), 0] ![(-1:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.singleton_adj_00_L

/--
[singleton_adj_00_B](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singleton_adj_00_B_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.singleton_adj_00_B

/--
[singleton_adj_L_LB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singleton_adj_L_LB_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.singleton_adj_L_LB

/--
[singleton_adj_B_LB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singleton_adj_B_LB_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Adj ![(0:ℤ), -1] ![(-1:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.singleton_adj_B_LB

/--
[mem_singletonBoundarySupport_00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_singletonBoundarySupport_00_eq :
-- imply
  (![(0:ℤ), 0] : Site 2) ∈ singletonBoundarySupport := by
-- proof
  apply StatMech.Lattice.mem_singletonBoundarySupport_00

/--
[singletonBoundarySupport_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singletonBoundarySupport_cases_eq
  {v : Site 2}
-- given
  (hv : v ∈ singletonBoundarySupport) :
-- imply
  v = ![(0:ℤ), 0] ∨ v = ![(-1:ℤ), 0] ∨ v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.singletonBoundarySupport_cases hv

/--
[singleton_walk_from_00](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singleton_walk_from_00_eq
  {v : Site 2}
-- given
  (hv : v ∈ singletonBoundarySupport) :
-- imply
  ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk ![(0:ℤ), 0] v, ∀ w ∈ p.support, w ∈ singletonBoundarySupport := by
-- proof
  apply StatMech.Lattice.singleton_walk_from_00 hv

/--
[singletonOrigin_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singletonOrigin_faceBoundaryConnected_eq :
-- imply
  FaceBoundaryConnected (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) singletonBoundarySupport := by
-- proof
  apply StatMech.Lattice.singletonOrigin_faceBoundaryConnected

/--
[support_singletonOrigin_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma support_singletonOrigin_subset_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support ⊆ (singletonBoundarySupport : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.support_singletonOrigin_subset

/--
[singletonOrigin_single_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma singletonOrigin_single_dualCircuit_eq :
-- imply
  ∃ c : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk ![(0:ℤ), 0] ![(0:ℤ), 0], c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.singletonOrigin_single_dualCircuit

/--
[mem_boxCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxCluster_eq
  {m n : ℕ}
  {x : Site 2} :
-- imply
  x ∈ boxCluster m n ↔ 0 ≤ x 0 ∧ x 0 ≤ m ∧ 0 ≤ x 1 ∧ x 1 ≤ n := by
-- proof
  apply StatMech.Lattice.mem_boxCluster m n x

/--
[mem_box_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_box_coords_eq
  {m n : ℕ}
  {p q : ℤ} :
-- imply
  (![p, q] : Site 2) ∈ (↑(boxCluster m n) : Set (Site 2)) ↔ 0 ≤ p ∧ p ≤ m ∧ 0 ≤ q ∧ q ≤ n := by
-- proof
  apply StatMech.Lattice.mem_box_coords m n p q

/--
[origin_mem_boxCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma origin_mem_boxCluster_eq
  {m n : ℕ} :
-- imply
  origin 2 ∈ boxCluster m n := by
-- proof
  apply StatMech.Lattice.origin_mem_boxCluster m n

/--
[boxR_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxR_step_eq
  {m n : ℕ}
  {a b : ℤ}
-- given
  (h0 : 0 ≤ a)
  (h1 : a + 1 ≤ m)
  (h2 : 0 ≤ b)
  (h3 : b ≤ n) :
-- imply
  (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Lattice.boxR_step m n a b h0 h1 h2 h3

/--
[boxT_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxT_step_eq
  {m n : ℕ}
  {a b : ℤ}
-- given
  (h0 : 0 ≤ a)
  (h1 : a ≤ m)
  (h2 : 0 ≤ b)
  (h3 : b + 1 ≤ n) :
-- imply
  (latticeOn (↑(boxCluster m n) : Set (Site 2))).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Lattice.boxT_step m n a b h0 h1 h2 h3

/--
[reach_xaxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma reach_xaxis_eq
  {m n : ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ m) :
-- imply
  (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![(0:ℤ), 0] ![(k:ℤ), 0] := by
-- proof
  apply StatMech.Lattice.reach_xaxis m n k hk

/--
[reach_ycol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma reach_ycol_eq
  {m n : ℕ}
  {a : ℤ}
  {k : ℕ}
-- given
  (ha0 : 0 ≤ a)
  (ham : a ≤ m)
  (hk : k ≤ n) :
-- imply
  (latticeOn (↑(boxCluster m n) : Set (Site 2))).Reachable ![a, 0] ![a, (k:ℤ)] := by
-- proof
  apply StatMech.Lattice.reach_ycol m n a ha0 ham k hk

/--
[boxCluster_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxCluster_isConnectedCluster_eq
  {m n : ℕ} :
-- imply
  IsConnectedCluster (boxCluster m n) := by
-- proof
  apply StatMech.Lattice.boxCluster_isConnectedCluster m n

/--
[mem_boxFrame_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_bottom_eq
  {m n : ℕ}
  {a : ℤ}
-- given
  (h0 : -1 ≤ a)
  (h1 : a ≤ m) :
-- imply
  (![a, -1] : Site 2) ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_bottom m n a h0 h1

/--
[mem_boxFrame_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_top_eq
  {m n : ℕ}
  {a : ℤ}
-- given
  (h0 : -1 ≤ a)
  (h1 : a ≤ m) :
-- imply
  (![a, (n:ℤ)] : Site 2) ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_top m n a h0 h1

/--
[mem_boxFrame_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_left_eq
  {m n : ℕ}
  {b : ℤ}
-- given
  (h0 : -1 ≤ b)
  (h1 : b ≤ n) :
-- imply
  (![(-1:ℤ), b] : Site 2) ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_left m n b h0 h1

/--
[mem_boxFrame_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_right_eq
  {m n : ℕ}
  {b : ℤ}
-- given
  (h0 : -1 ≤ b)
  (h1 : b ≤ n) :
-- imply
  (![(m:ℤ), b] : Site 2) ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_right m n b h0 h1

/--
[boxFrame_bottom_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_bottom_adj_eq
  {m n : ℕ}
  {a : ℤ}
-- given
  (h0 : 0 ≤ a + 1)
  (h1 : a + 1 ≤ m) :
-- imply
  (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, -1] ![a + 1, -1] := by
-- proof
  apply StatMech.Lattice.boxFrame_bottom_adj m n a h0 h1

/--
[boxFrame_top_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_top_adj_eq
  {m n : ℕ}
  {a : ℤ}
-- given
  (h0 : 0 ≤ a + 1)
  (h1 : a + 1 ≤ m) :
-- imply
  (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![a, (n:ℤ)] ![a + 1, (n:ℤ)] := by
-- proof
  apply StatMech.Lattice.boxFrame_top_adj m n a h0 h1

/--
[boxFrame_right_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_right_adj_eq
  {m n : ℕ}
  {b : ℤ}
-- given
  (h0 : 0 ≤ b + 1)
  (h1 : b + 1 ≤ n) :
-- imply
  (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(m:ℤ), b] ![(m:ℤ), b + 1] := by
-- proof
  apply StatMech.Lattice.boxFrame_right_adj m n b h0 h1

/--
[boxFrame_left_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_left_adj_eq
  {m n : ℕ}
  {b : ℤ}
-- given
  (h0 : 0 ≤ b + 1)
  (h1 : b + 1 ≤ n) :
-- imply
  (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Adj ![(-1:ℤ), b] ![(-1:ℤ), b + 1] := by
-- proof
  apply StatMech.Lattice.boxFrame_left_adj m n b h0 h1

/--
[boxFrame_bottom_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_bottom_walk_eq
  {m n : ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ m + 1) :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(k:ℤ) - 1, -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_bottom_walk m n k hk

/--
[boxFrame_left_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_left_walk_eq
  {m n : ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ n + 1) :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(-1:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_left_walk m n k hk

/--
[boxFrame_right_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_right_walk_eq
  {m n : ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ n + 1) :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(m:ℤ), -1] ![(m:ℤ), (k:ℤ) - 1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_right_walk m n k hk

/--
[boxFrame_top_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_top_walk_eq
  {m n : ℕ}
  {k : ℕ}
-- given
  (hk : k ≤ m + 1) :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), (n:ℤ)] ![(k:ℤ) - 1, (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_top_walk m n k hk

/--
[mem_boxFrame_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_cases_eq
  {m n : ℕ}
  {v : Site 2}
-- given
  (hv : v ∈ boxFrame m n) :
-- imply
  (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, -1]) ∨ (∃ a : ℤ, -1 ≤ a ∧ a ≤ m ∧ v = ![a, (n:ℤ)]) ∨ (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(-1:ℤ), b]) ∨ (∃ b : ℤ, -1 ≤ b ∧ b ≤ n ∧ v = ![(m:ℤ), b]) := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_cases m n v hv

/--
[mem_boxFrame_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma mem_boxFrame_corner_eq
  {m n : ℕ} :
-- imply
  (![(-1:ℤ), -1] : Site 2) ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.mem_boxFrame_corner m n

/--
[boxFrame_bottom_to_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_bottom_to_corner_eq
  {m n : ℕ} :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(m:ℤ), -1], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_bottom_to_corner m n

/--
[boxFrame_left_to_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_left_to_corner_eq
  {m n : ℕ} :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(-1:ℤ), (n:ℤ)], ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_left_to_corner m n

/--
[boxFrame_walk_from_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxFrame_walk_from_corner_eq
  {m n : ℕ}
  {v : Site 2}
-- given
  (hv : v ∈ boxFrame m n) :
-- imply
  ∃ p : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] v, ∀ w ∈ p.support, w ∈ boxFrame m n := by
-- proof
  apply StatMech.Lattice.boxFrame_walk_from_corner m n hv

/--
[boxCluster_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxCluster_faceBoundaryConnected_eq
  {m n : ℕ} :
-- imply
  FaceBoundaryConnected (↑(boxCluster m n) : Set (Site 2)) (boxFrame m n) := by
-- proof
  apply StatMech.Lattice.boxCluster_faceBoundaryConnected m n

/--
[straddle_implies_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma straddle_implies_frame_eq
  {m n : ℕ}
  {a b : ℤ}
-- given
  (hin : (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ (0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨ (0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n))
  (hout : ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b ∧ b ≤ n) ∨ ¬(0 ≤ a + 1 ∧ a + 1 ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n) ∨ ¬(0 ≤ a ∧ a ≤ m ∧ 0 ≤ b + 1 ∧ b + 1 ≤ n)) :
-- imply
  (-1 ≤ a ∧ a ≤ m ∧ b = -1) ∨ (-1 ≤ a ∧ a ≤ m ∧ b = (n:ℤ)) ∨ (a = -1 ∧ -1 ≤ b ∧ b ≤ n) ∨ (a = (m:ℤ) ∧ -1 ≤ b ∧ b ≤ n) := by
-- proof
  apply StatMech.Lattice.straddle_implies_frame m n a b hin hout

/--
[bdInd_eq_zero_of_sameSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma bdInd_eq_zero_of_sameSide_eq
  {m n : ℕ}
  {x y : Site 2}
-- given
  (h : (x ∈ (↑(boxCluster m n) : Set (Site 2))) ↔ (y ∈ (↑(boxCluster m n) : Set (Site 2)))) :
-- imply
  bdInd (↑(boxCluster m n) : Set (Site 2)) x y = 0 := by
-- proof
  apply StatMech.Lattice.bdInd_eq_zero_of_sameSide m n x y h

/--
[support_boxCluster_subset_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma support_boxCluster_subset_frame_eq
  {m n : ℕ} :
-- imply
  (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).support ⊆ (boxFrame m n : Set (Site 2)) := by
-- proof
  apply StatMech.Lattice.support_boxCluster_subset_frame m n

/--
[boxCluster_single_dualCircuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsBoundaryConnected.lean)
-/
@[path]
private lemma boxCluster_single_dualCircuit_eq
  {m n : ℕ} :
-- imply
  ∃ c : (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).Walk ![(-1:ℤ), -1] ![(-1:ℤ), -1], c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑(boxCluster m n) : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Lattice.boxCluster_single_dualCircuit m n


-- created on 2026-10-23

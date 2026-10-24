import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[cfc_T_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_T_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (cfc_T ω n).IsAcyclic := by
-- proof
  apply StatMech.Percolation.cfc_T_acyclic ω n

/--
[cfc_T_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_T_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {u v : Site d}
-- given
  (h : (cfc_T ω n).Adj u v) :
-- imply
  (openSubgraph d ω).Adj u v := by
-- proof
  apply StatMech.Percolation.cfc_T_open ω n u v h

/--
[cfc_T_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_T_support_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {u v : Site d}
-- given
  (h : (cfc_T ω n).Adj u v) :
-- imply
  u ∈ box d (n + 1) := by
-- proof
  apply StatMech.Percolation.cfc_T_support ω n u v h

/--
[cfc_induce_reachable_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_induce_reachable_of_walk_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  ∀ {a b : Site d} (w : (openSubgraph d ω).Walk a b), (∀ v ∈ w.support, v ∈ box d (n + 1)) → ∀ (ha : a ∈ box d (n + 1)) (hb : b ∈ box d (n + 1)), (cfc_Gbox ω n).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Percolation.cfc_induce_reachable_of_walk ω n

/--
[cfc_map_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_map_reachable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a b : (↑(box d (n + 1)) : Type)}
-- given
  (h : (cfc_F ω n).Reachable a b) :
-- imply
  (cfc_T ω n).Reachable (a : Site d) (b : Site d) := by
-- proof
  apply StatMech.Percolation.cfc_map_reachable ω n h

/--
[cfc_removeSite_walk_to_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_removeSite_walk_to_ambient_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {a b : Site d}
  {w : (openSubgraph d (removeSite x ω)).Walk a b} :
-- imply
  ∃ w' : (openSubgraph d ω).Walk a b, w'.support = w.support := by
-- proof
  apply StatMech.Percolation.cfc_removeSite_walk_to_ambient ω x w

/--
[cfc_x_reaches_z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_x_reaches_z_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a z : Site d}
  {w : (openSubgraph d (removeSite x ω)).Walk a z}
-- given
  (hxbox : x ∈ box d n)
  (hadjxa : (openSubgraph d ω).Adj x a)
  (hwx : x ∉ w.support)
  (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1)) :
-- imply
  (cfc_T ω n).Reachable x z := by
-- proof
  apply StatMech.Percolation.cfc_x_reaches_z ω n hxbox hadjxa w hwx hwbox

/--
[cfc_extract_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_extract_arm_eq
  {d : ℕ}
  {T : SimpleGraph (Site d)}
  {x z : Site d}
-- given
  (h : T.Reachable x z)
  (hxz : x ≠ z) :
-- imply
  ∃ (c : Site d) (rest : T.Walk c z), T.Adj x c ∧ x ∉ rest.support := by
-- proof
  apply StatMech.Percolation.cfc_extract_arm h hxz

/--
[cfc_per_arm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_per_arm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a z : Site d}
  {w : (openSubgraph d (removeSite x ω)).Walk a z}
-- given
  (hxbox : x ∈ box d n)
  (hadjxa : (openSubgraph d ω).Adj x a)
  (hwx : x ∉ w.support)
  (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1))
  (hzx : z ≠ x) :
-- imply
  ∃ c : Site d, (cfc_T ω n).Adj x c ∧ (∃ wt : (cfc_T ω n).Walk c z, x ∉ wt.support) ∧ Connected d (removeSite x ω) c z := by
-- proof
  apply StatMech.Percolation.cfc_per_arm ω n hxbox hadjxa w hwx hwbox hzx

/--
[cfc_walk_crossing_confined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_walk_crossing_confined_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {x y : V}
  {w : G.Walk x y}
-- given
  (p : V → Prop)
  (hx0 : p x)
  (hy0 : ¬ p y) :
-- imply
  ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧ ∃ wxa : G.Walk x a, ∀ v ∈ wxa.support, p v := by
-- proof
  apply StatMech.Percolation.cfc_walk_crossing_confined G p w hx0 hy0

/--
[cfc_arm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_arm_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hn : 1 ≤ n)
  (hax : a ≠ x)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support ∧ ∀ v ∈ w.support, v ∈ box d n := by
-- proof
  apply StatMech.Percolation.cfc_arm_reaches_boundary ω n hn x a hax habox hinf

/--
[cfc_neighbour_outside_box_imp_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_neighbour_outside_box_imp_boundary_eq
  {d : ℕ}
  {n : ℕ}
  {x c : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : x ∈ box d n)
  (hadj : (hypercubicLattice d).Adj x c)
  (hc : c ∉ box d n) :
-- imply
  x ∉ box d (n - 1) := by
-- proof
  apply StatMech.Percolation.cfc_neighbour_outside_box_imp_boundary hn hx hadj hc

/--
[cfc_trif_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_trif_data_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {c0 : Fin 3 → Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (c0 i))
  (hne : ∀ i, c0 i ≠ x)
  (hcbox : ∀ i, c0 i ∈ box d n)
  (hcut : ¬ Connected d (removeSite x ω) (c0 0) (c0 1) ∧ ¬ Connected d (removeSite x ω) (c0 0) (c0 2) ∧ ¬ Connected d (removeSite x ω) (c0 1) (c0 2))
  (hinf : ∀ i, (cluster d (removeSite x ω) (c0 i)).Infinite) :
-- imply
  ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d), (∀ i, (cfc_T ω n).Adj x (c i)) ∧ (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧ ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧ ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧ (∀ i, zr i ∈ vertexBoundary d n ∧ ∃ w : (cfc_T ω n).Walk (c i) (zr i), x ∉ w.support) := by
-- proof
  apply StatMech.Percolation.cfc_trif_data ω n hn hxbox c0 hadj hne hcbox hcut hinf

/--
[cfc_armForestReaching_of_canonical_armsInBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_armForestReaching_of_canonical_armsInBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  sfa_ArmForestReaching ω n := by
-- proof
  apply StatMech.Percolation.cfc_armForestReaching_of_canonical_armsInBox ω n hn hcanon harmbox hexists

/--
[cfc_Tcount_le_boundary_of_no_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_Tcount_le_boundary_of_no_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.cfc_Tcount_le_boundary_of_no_trif ω n hno

/--
[cfc_Tcount_le_boundary_of_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonForestCount.lean)
-/
@[path]
private lemma cfc_Tcount_le_boundary_of_canonical_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.cfc_Tcount_le_boundary_of_canonical ω n hn hcanon harmbox


-- created on 2026-10-23

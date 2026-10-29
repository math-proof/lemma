import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part4
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[ray34_mem_avoidCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_mem_avoidCluster_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v w : V} :
-- imply
  w ∈ ray34_AvoidCluster G S v ↔ ray34_AvoidReach G S v w := by
-- proof
  apply StatMech.Walls.ray34_mem_avoidCluster

/--
[ray34_avoidReach_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidReach_refl_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (hv : v ∉ S) :
-- imply
  ray34_AvoidReach G S v v := by
-- proof
  apply StatMech.Walls.ray34_avoidReach_refl G S hv

/--
[ray34_avoidReach_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidReach_symm_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v w : V}
-- given
  (h : ray34_AvoidReach G S v w) :
-- imply
  ray34_AvoidReach G S w v := by
-- proof
  apply StatMech.Walls.ray34_avoidReach_symm h

/--
[ray34_avoidReach_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidReach_trans_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {u v w : V}
-- given
  (huv : ray34_AvoidReach G S u v)
  (hvw : ray34_AvoidReach G S v w) :
-- imply
  ray34_AvoidReach G S u w := by
-- proof
  apply StatMech.Walls.ray34_avoidReach_trans huv hvw

/--
[ray34_avoidCluster_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_avoids_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v w : V}
-- given
  (h : w ∈ ray34_AvoidCluster G S v) :
-- imply
  w ∉ S := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_avoids h

/--
[ray34_self_mem_avoidCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_self_mem_avoidCluster_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (hv : v ∉ S) :
-- imply
  v ∈ ray34_AvoidCluster G S v := by
-- proof
  apply StatMech.Walls.ray34_self_mem_avoidCluster G S hv

/--
[ray34_notMem_of_avoidCluster_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_notMem_of_avoidCluster_nonempty_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (h : (ray34_AvoidCluster G S v).Nonempty) :
-- imply
  v ∉ S := by
-- proof
  apply StatMech.Walls.ray34_notMem_of_avoidCluster_nonempty h

/--
[ray34_avoidCluster_eq_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_eq_of_reach_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {v w : V}
-- given
  (h : ray34_AvoidReach G S v w) :
-- imply
  ray34_AvoidCluster G S v = ray34_AvoidCluster G S w := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_eq_of_reach h

/--
[ray34_avoidCluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_mono_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S T : Set V}
  {v : V}
-- given
  (hST : S ⊆ T) :
-- imply
  ray34_AvoidCluster G T v ⊆ ray34_AvoidCluster G S v := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_mono hST v

/--
[ray34_avoidCluster_diff_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_diff_subset_biUnion_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {S : Set V}
  [DecidablePred (· ∉ S)]
  {v : V} :
-- imply
  ray34_AvoidCluster G S v \ {v} ⊆ ⋃ w ∈ (G.neighborFinset v).filter (· ∉ S), ray34_AvoidCluster G (insert v S) w := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_diff_subset_biUnion v

/--
[ray34_konig_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_konig_step_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {S : Set V}
  {v : V}
-- given
  (hv : v ∉ S)
  (hinf : (ray34_AvoidCluster G S v).Infinite) :
-- imply
  ∃ w, G.Adj v w ∧ w ∉ S ∧ w ∈ ray34_AvoidCluster G S v ∧ (ray34_AvoidCluster G (insert v S) w).Infinite := by
-- proof
  apply StatMech.Walls.ray34_konig_step hv hinf

/--
[ray34_kstep_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_kstep_adj_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {s : ray34_KState G} :
-- imply
  G.Adj s.1.2 (ray34_kstep G s).1.2 := by
-- proof
  apply StatMech.Walls.ray34_kstep_adj G s

/--
[ray34_kstep_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_kstep_fst_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {s : ray34_KState G} :
-- imply
  (ray34_kstep G s).1.1 = insert s.1.2 s.1.1 := by
-- proof
  apply StatMech.Walls.ray34_kstep_fst G s

/--
[ray34_konig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_konig_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {S : Set V}
  {v : V}
-- given
  (hv : v ∉ S)
  (hinf : (ray34_AvoidCluster G S v).Infinite) :
-- imply
  ∃ r : ℕ → V, r 0 = v ∧ Function.Injective r ∧ (∀ k, G.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ S) := by
-- proof
  apply StatMech.Walls.ray34_konig G hv hinf

/--
[ray34_avoidCluster_diff_subset_biUnion_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_diff_subset_biUnion_gen_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {S : Set V}
  {v t : V} :
-- imply
  ray34_AvoidCluster G S v \ {t} ⊆ ray34_AvoidCluster G (insert t S) v ∪ ⋃ w ∈ (G.neighborFinset t).filter (· ∉ insert t S), ray34_AvoidCluster G (insert t S) w := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_diff_subset_biUnion_gen v t

/--
[ray34_root_mem_of_piece_meets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_root_mem_of_piece_meets_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {S : Set V}
  {t v w z : V}
-- given
  (hz1 : z ∈ ray34_AvoidCluster G (insert t S) w)
  (hz2 : z ∈ ray34_AvoidCluster G S v) :
-- imply
  w ∈ ray34_AvoidCluster G S v := by
-- proof
  apply StatMech.Walls.ray34_root_mem_of_piece_meets hz1 hz2

/--
[ray34_avoidCluster_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_step_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {S : Set V}
  {v : V}
  {t : V}
-- given
  (hinf : (ray34_AvoidCluster G S v).Infinite) :
-- imply
  ∃ b, b ∈ ray34_AvoidCluster G S v ∧ (ray34_AvoidCluster G (insert t S) b).Infinite := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_step hinf t

/--
[ray34_infinite_avoidCluster_of_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_infinite_avoidCluster_of_finset_eq
  {d : ℕ}
  [DecidableEq V]
  {G : SimpleGraph V}
  [LocallyFinite G]
  {v : V}
  {T : Finset V}
-- given
  (hinf : (ray34_AvoidCluster G ∅ v).Infinite) :
-- imply
  ∃ b, b ∈ ray34_AvoidCluster G ∅ v ∧ (ray34_AvoidCluster G (↑T) b).Infinite := by
-- proof
  apply StatMech.Walls.ray34_infinite_avoidCluster_of_finset hinf T

/--
[ray34_avoidCluster_empty_eq_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_empty_eq_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d} :
-- imply
  ray34_AvoidCluster (openSubgraph d ω) ∅ v = cluster d ω v := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_empty_eq_cluster ω v

/--
[ray34_connected_of_avoidReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_connected_of_avoidReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {v w : Site d}
-- given
  (h : ray34_AvoidReach (openSubgraph d ω) S v w) :
-- imply
  Connected d ω v w := by
-- proof
  apply StatMech.Walls.ray34_connected_of_avoidReach h

/--
[ray34_Tavoiding_ray_of_infinite_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_Tavoiding_ray_of_infinite_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {v : Site d}
  {T : Finset (Site d)}
-- given
  (hinf : (cluster d ω v).Infinite) :
-- imply
  ∃ b : Site d, Connected d ω v b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ T) := by
-- proof
  apply StatMech.Walls.ray34_Tavoiding_ray_of_infinite_cluster ω hinf T

/--
[ray34_adj_removeSite_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_adj_removeSite_of_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a c : Site d}
-- given
  (hadj : (openSubgraph d ω).Adj a c)
  (ha : a ≠ x)
  (hc : c ≠ x) :
-- imply
  (openSubgraph d (removeSite x ω)).Adj a c := by
-- proof
  apply StatMech.Walls.ray34_adj_removeSite_of_adj hadj ha hc

/--
[ray34_removeSite_Tavoiding_ray_of_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_removeSite_Tavoiding_ray_of_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {T : Finset (Site d)}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ b : Site d, Connected d ω x b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, (openSubgraph d (removeSite x ω)).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ T) := by
-- proof
  apply StatMech.Walls.ray34_removeSite_Tavoiding_ray_of_trif ω hinf T

/--
[bc34_TavoidingRayData_of_TavoidingCutArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma bc34_TavoidingRayData_of_TavoidingCutArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc34_TavoidingCutArmData ω n rank) :
-- imply
  bc33_TavoidingRayData ω n rank := by
-- proof
  apply StatMech.Walls.bc34_TavoidingRayData_of_TavoidingCutArmData ω n rank h

/--
[ray34_avoidReach_removeSite_iff_connected_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidReach_removeSite_iff_connected_removeSites_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : Finset (Site d)}
  {x b w : Site d}
-- given
  (hxT : x ∈ T)
  (hbT : b ∉ (↑T : Set (Site d))) :
-- imply
  ray34_AvoidReach (openSubgraph d (removeSite x ω)) (↑T) b w ↔ Connected d (removeSites T ω) b w := by
-- proof
  apply StatMech.Walls.ray34_avoidReach_removeSite_iff_connected_removeSites hxT hbT

/--
[ray34_avoidCluster_removeSite_eq_cluster_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma ray34_avoidCluster_removeSite_eq_cluster_removeSites_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : Finset (Site d)}
  {x b : Site d}
-- given
  (hxT : x ∈ T)
  (hbT : b ∉ (↑T : Set (Site d))) :
-- imply
  ray34_AvoidCluster (openSubgraph d (removeSite x ω)) (↑T) b = cluster d (removeSites T ω) b := by
-- proof
  apply StatMech.Walls.ray34_avoidCluster_removeSite_eq_cluster_removeSites hxT hbT

/--
[bc34_TavoidingRayData_of_globalCutArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma bc34_TavoidingRayData_of_globalCutArm_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {b : Site d → Site d}
-- given
  (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsplit : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x < rank y → ¬ Connected d (removeSite y ω) (b y) (b x)) :
-- imply
  bc33_TavoidingRayData ω n rank := by
-- proof
  apply StatMech.Walls.bc34_TavoidingRayData_of_globalCutArm ω n rank b hbdata hsplit

/--
[bc34_burton_keane_bernoulli_of_globalCutArm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma bc34_burton_keane_bernoulli_of_globalCutArm_eq
  {d : ℕ}
  {rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ}
  {bfun : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → Site d}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank ω n x ≠ rank ω n y)
  (hbdata : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ x, x ∈ box d n → IsTrifurcation d ω x → bfun ω n x ∈ box d n ∧ Connected d ω x (bfun ω n x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (bfun ω n x)).Infinite)
  (hsplit : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank ω n x < rank ω n y → ¬ Connected d (removeSite y ω) (bfun ω n y) (bfun ω n x))
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc34_burton_keane_bernoulli_of_globalCutArm hd p hp1 hp0 rank bfun hinj hbdata hsplit htrif

/--
[bc34_TavoidingRayData_of_threeChain_globalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc34ray.lean)
-/
@[path]
private lemma bc34_TavoidingRayData_of_threeChain_globalCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ m g : Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hmbox : m ∈ box d n)
  (hgbox : g ∈ box d n)
  (hx0m : x₀ ≠ m)
  (hx0g : x₀ ≠ g)
  (hmg : m ≠ g)
  (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
  (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x → b x ∈ box d n ∧ Connected d ω x (b x) ∧ (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc33_TavoidingRayData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc34_TavoidingRayData_of_threeChain_globalCut ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree harm hsxm hsxg hsmg


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc31globalarm.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc31_removeSites_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_removeSites_isolated_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {t : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (htT : t ∈ T) :
-- imply
  ¬ (openSubgraph d (removeSites T ω)).Adj t y := by
-- proof
  apply StatMech.Walls.bc31_removeSites_isolated htT ω y

/--
[bc31_walk_avoids_removeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_walk_avoids_removeSites_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d (removeSites T ω)).Walk a b}
-- given
  (haT : a ∉ T) :
-- imply
  ∀ z ∈ w.support, z ∉ T := by
-- proof
  apply StatMech.Walls.bc31_walk_avoids_removeSites haT w

/--
[bc31_edge_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_edge_transfer_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (huT : u ∉ T)
  (hvT : v ∉ T)
  (h : (openSubgraph d (removeSite x ω)).Adj u v) :
-- imply
  (openSubgraph d (removeSites T ω)).Adj u v := by
-- proof
  apply StatMech.Walls.bc31_edge_transfer ω huT hvT h

/--
[bc31_walk_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_walk_transfer_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {x a b : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d (removeSite x ω)).Walk a b}
-- given
  (havoid : ∀ z ∈ w.support, z ∉ T) :
-- imply
  Connected d (removeSites T ω) a b := by
-- proof
  apply StatMech.Walls.bc31_walk_transfer ω w havoid

/--
[bc31_infinite_globalCut_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_infinite_globalCut_reaches_boundary_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (haT : a ∉ T)
  (habox : a ∈ box d n)
  (hinf : (cluster d (removeSites T ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d n, ∃ w : (openSubgraph d (removeSites T ω)).Walk a z, ∀ v ∈ w.support, v ∉ T := by
-- proof
  apply StatMech.Walls.bc31_infinite_globalCut_reaches_boundary T ω n hn haT habox hinf

/--
[bc31_globalCut_infinite_of_escaping](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_globalCut_infinite_of_escaping_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hesc : ∀ m : ℕ, ∃ y, y ∉ box d m ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk a y, ∀ z ∈ w.support, z ∉ T) :
-- imply
  (cluster d (removeSites T ω) a).Infinite := by
-- proof
  apply StatMech.Walls.bc31_globalCut_infinite_of_escaping ω hesc

/--
[bc31_support_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_support_connected_eq
  {d : ℕ}
  {x a b z : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d (removeSite x ω)).Walk a b}
-- given
  (hz : z ∈ w.support) :
-- imply
  Connected d (removeSite x ω) a z := by
-- proof
  apply StatMech.Walls.bc31_support_connected ω w hz

/--
[bc31_globalCut_infinite_of_singleCut_Tfree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_globalCut_infinite_of_singleCut_Tfree_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hinf : (cluster d (removeSite x ω) a).Infinite)
  (hTfree : ∀ z, Connected d (removeSite x ω) a z → z ∉ T) :
-- imply
  (cluster d (removeSites T ω) a).Infinite := by
-- proof
  apply StatMech.Walls.bc31_globalCut_infinite_of_singleCut_Tfree ω hinf hTfree

/--
[bc31_globalCutDownArmData_of_TfreeDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_globalCutDownArmData_of_TfreeDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (h : bc31_TfreeDownArmData ω n rank) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc31_globalCutDownArmData_of_TfreeDownArmData ω n rank h

/--
[bc31_bundledRootedDownArmForest_of_TfreeDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_bundledRootedDownArmForest_of_TfreeDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc31_TfreeDownArmData ω n rank) :
-- imply
  bc29_BundledRootedDownArmForest ω n := by
-- proof
  apply StatMech.Walls.bc31_bundledRootedDownArmForest_of_TfreeDownArmData ω n rank hinj h

/--
[bc31_Tcount_le_boundary_of_TfreeDownArmData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_Tcount_le_boundary_of_TfreeDownArmData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
-- given
  (hn : 1 ≤ n)
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → x ≠ y → Connected d ω x y → rank x ≠ rank y)
  (h : bc31_TfreeDownArmData ω n rank) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc31_Tcount_le_boundary_of_TfreeDownArmData ω n hn rank hinj h

/--
[bc31_removeSite_notConnected_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_removeSite_notConnected_self_eq
  {d : ℕ}
  {x a : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hax : a ≠ x) :
-- imply
  ¬ Connected d (removeSite x ω) a x := by
-- proof
  apply StatMech.Walls.bc31_removeSite_notConnected_self ω hax

/--
[bc31_globalCutDownArmData_of_uniqueTrif_singleCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_globalCutDownArmData_of_uniqueTrif_singleCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {rank : Site d → ℕ ×ₗ ℕ}
  {x₀ a : Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (htri0 : IsTrifurcation d ω x₀)
  (habox : a ∈ box d n)
  (haconn : Connected d ω x₀ a)
  (hax0 : a ≠ x₀)
  (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
  (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
-- imply
  bc30_GlobalCutDownArmData ω n rank := by
-- proof
  apply StatMech.Walls.bc31_globalCutDownArmData_of_uniqueTrif_singleCut ω n rank hx0box htri0 habox haconn hax0 hainf huniq

/--
[bc31_TfreeDownArmData_clauses_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_TfreeDownArmData_clauses_consistent_eq
  {d : ℕ} :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1), (∀ z, Connected 1 (removeSite y ω) by' z → z ≠ y ∧ z ≠ bx) ∧ ¬ Connected 1 (removeSite y ω) by' bx := by
-- proof
  apply StatMech.Walls.bc31_TfreeDownArmData_clauses_consistent

/--
[bc31_TfreeDownArmData_of_threeChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_TfreeDownArmData_of_threeChain_eq
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
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧ (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
  (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧ (cluster d (removeSite m ω) (b m)).Infinite ∧ (∀ z, Connected d (removeSite m ω) (b m) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
  (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧ (cluster d (removeSite g ω) (b g)).Infinite ∧ (∀ z, Connected d (removeSite g ω) (b g) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
  (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
  (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
  (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
-- imply
  bc31_TfreeDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc31_TfreeDownArmData_of_threeChain ω n b hx0box hmbox hgbox hx0m hx0g hmg hthree hbx0 hbm hbg hsxm hsxg hsmg

/--
[bc31_TfreeDownArmData_of_claw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean)
-/
@[path]
private lemma bc31_TfreeDownArmData_of_claw_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x₀ : Site d}
  {y : Fin 3 → Site d}
  {b : Site d → Site d}
-- given
  (hx0box : x₀ ∈ box d n)
  (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
  (hyinj : Function.Injective y)
  (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
  (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧ (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧ (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ ∀ i, z ≠ y i))
  (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧ (cluster d (removeSite (y i) ω) (b (y i))).Infinite ∧ (∀ z, Connected d (removeSite (y i) ω) (b (y i)) z → z ≠ x₀ ∧ ∀ j, z ≠ y j))
  (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
  (hssib : ∀ i j : Fin 3, (j : ℕ) < i → ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
-- imply
  bc31_TfreeDownArmData ω n (fun z => if z = x₀ then toLex (0, 0) else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
-- proof
  apply StatMech.Walls.bc31_TfreeDownArmData_of_claw ω n x₀ y b hx0box hydata hyinj hsingle hbx0 hby hsx0 hssib


-- created on 2026-10-23

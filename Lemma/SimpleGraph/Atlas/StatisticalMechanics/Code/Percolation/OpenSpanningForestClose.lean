import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.OsfDoubleStar


/--
[osf_spanForest_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_spec_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (osf_spanForest G) := by
-- proof
  apply StatMech.Percolation.osf_spanForest_spec G

/--
[osf_spanForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  (osf_spanForest G).IsAcyclic := by
-- proof
  apply StatMech.Percolation.osf_spanForest_acyclic G

/--
[osf_spanForest_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_le_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V} :
-- imply
  osf_spanForest G ≤ G := by
-- proof
  apply StatMech.Percolation.osf_spanForest_le G

/--
[osf_spanForest_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_reachable_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  {u v : V}
-- given
  (h : G.Adj u v) :
-- imply
  (osf_spanForest G).Reachable u v := by
-- proof
  apply StatMech.Percolation.osf_spanForest_reachable G h

/--
[osf_spanForest_reachable_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_reachable_of_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  {u v : V}
-- given
  (h : G.Reachable u v) :
-- imply
  (osf_spanForest G).Reachable u v := by
-- proof
  apply StatMech.Percolation.osf_spanForest_reachable_of G h

/--
[osf_spanForest_degree_pos_of_reachable_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_degree_pos_of_reachable_ne_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel (osf_spanForest G).Adj]
  {u v : V}
-- given
  (hv : v ≠ u)
  (h : G.Reachable u v) :
-- imply
  1 ≤ (osf_spanForest G).degree u := by
-- proof
  apply StatMech.Percolation.osf_spanForest_degree_pos_of_reachable_ne G hv h

/--
[osf_spanForest_of_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_of_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
-- given
  (hG : G.IsAcyclic) :
-- imply
  osf_spanForest G = G := by
-- proof
  apply StatMech.Percolation.osf_spanForest_of_acyclic G hG

/--
[osf_spanForest_degree_of_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_spanForest_degree_of_acyclic_eq
  {d : ℕ}
  [Fintype V]
  {F₀ : SimpleGraph V}
  [DecidableRel F₀.Adj]
  [DecidableRel (osf_spanForest F₀).Adj]
  {v : V}
-- given
  (hac : F₀.IsAcyclic) :
-- imply
  (osf_spanForest F₀).degree v = F₀.degree v := by
-- proof
  apply StatMech.Percolation.osf_spanForest_degree_of_acyclic F₀ hac v

/--
[osf_boxOpenForest_of_peeled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_boxOpenForest_of_peeled_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : osf_PeeledBoxForest ω n) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Percolation.osf_boxOpenForest_of_peeled ω n h

/--
[osf_peeledBoxForest_of_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_peeledBoxForest_of_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {Vset : Finset (Site d)}
  {F₀ : SimpleGraph (↑Vset : Type)}
  [DecidableRel F₀.Adj]
  {vx : Site d → (↑Vset : Type)}
  {b : Site d → Fin 3 → (↑Vset : Type)}
-- given
  (hVne : Nonempty (↑Vset : Type))
  (hac : F₀.IsAcyclic)
  (hπ0 : ∀ u v, F₀.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
  (hmin : ∀ v : (↑Vset : Type), 1 ≤ F₀.degree v)
  (htriData : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ((vx x : Site d) = x ∧ (∀ i, F₀.Reachable (vx x) (b x i) ∧ b x i ≠ vx x) ∧ (¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧ ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧ ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d))))
  (hleaf : ∀ v : (↑Vset : Type), F₀.degree v = 1 → (v : Site d) ∈ vertexBoundary d n) :
-- imply
  osf_PeeledBoxForest ω n := by
-- proof
  apply StatMech.Percolation.osf_peeledBoxForest_of_acyclic ω n Vset hVne F₀ hac vx b hπ0 hmin htriData hleaf

/--
[osf_peeledBoxForest_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_peeledBoxForest_star_eq
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
  osf_PeeledBoxForest ω n := by
-- proof
  apply StatMech.Percolation.osf_peeledBoxForest_star ω n a hsingle hadj habdry hxne hainj hsep

/--
[osf_singleTree_refutable_forest_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_singleTree_refutable_forest_survives_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hxbox : x ∈ box d n)
  (hxtri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (hytri : IsTrifurcation d ω y)
  (hsep : ¬ Connected d ω x y) :
-- imply
  ¬ bpr_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.osf_singleTree_refutable_forest_survives ω n hxbox hxtri hybox hytri hsep

/--
[jdsG_isTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma jdsG_isTree_eq
  {d : ℕ} :
-- imply
  jdsG.IsTree := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.jdsG_isTree

/--
[dsG_le_jdsG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma dsG_le_jdsG_eq
  {d : ℕ} :
-- imply
  dsG ≤ jdsG := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.dsG_le_jdsG

/--
[dsG_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma dsG_acyclic_eq
  {d : ℕ} :
-- imply
  dsG.IsAcyclic := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.dsG_acyclic

/--
[dsG_hub0_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma dsG_hub0_deg_eq
  {d : ℕ} :
-- imply
  dsG.degree 0 = 3 := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.dsG_hub0_deg

/--
[dsG_hub4_deg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma dsG_hub4_deg_eq
  {d : ℕ} :
-- imply
  dsG.degree 4 = 3 := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.dsG_hub4_deg

/--
[dsG_deg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma dsG_deg_pos_eq
  {d : ℕ}
  {v : Fin 8} :
-- imply
  1 ≤ dsG.degree v := by
-- proof
  apply StatMech.Percolation.OsfDoubleStar.dsG_deg_pos v

/--
[osf_peeledBoxForest_twoStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OpenSpanningForestClose.lean)
-/
@[path]
private lemma osf_peeledBoxForest_twoStar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x x' : Site d}
  {a a' : Fin 3 → Site d}
  {lab : Fin 8 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x ∨ y = x')
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (hadj' : ∀ i, (openSubgraph d ω).Adj x' (a' i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (habdry' : ∀ i, a' i ∈ vertexBoundary d n)
  (hxsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2))
  (hx'sep : ¬ Connected d (removeSite x' ω) (a' 0) (a' 1) ∧ ¬ Connected d (removeSite x' ω) (a' 0) (a' 2) ∧ ¬ Connected d (removeSite x' ω) (a' 1) (a' 2))
  (hlab : lab 0 = x ∧ lab 1 = a 0 ∧ lab 2 = a 1 ∧ lab 3 = a 2 ∧ lab 4 = x' ∧ lab 5 = a' 0 ∧ lab 6 = a' 1 ∧ lab 7 = a' 2)
  (hlabinj : Function.Injective lab) :
-- imply
  osf_PeeledBoxForest ω n := by
-- proof
  apply StatMech.Percolation.osf_peeledBoxForest_twoStar ω n a a' hsingle hadj hadj' habdry habdry' hxsep hx'sep lab hlab hlabinj


-- created on 2026-10-23

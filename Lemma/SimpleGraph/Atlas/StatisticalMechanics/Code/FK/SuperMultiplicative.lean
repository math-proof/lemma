import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
open SimpleGraph Filter Topology StatMech StatMech.FK


/--
[fsm_reach_inl_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_reach_inl_inl_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {a b : V} :
-- imply
  (G ⊕g H).Reachable (Sum.inl a) (Sum.inl b) ↔ G.Reachable a b := by
-- proof
  apply StatMech.FK.fsm_reach_inl_inl G H a b

/--
[fsm_reach_inr_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_reach_inr_inr_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {a b : W} :
-- imply
  (G ⊕g H).Reachable (Sum.inr a) (Sum.inr b) ↔ H.Reachable a b := by
-- proof
  apply StatMech.FK.fsm_reach_inr_inr G H a b

/--
[fsm_not_reach_inl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_not_reach_inl_inr_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {a : V}
  {b : W} :
-- imply
  ¬ (G ⊕g H).Reachable (Sum.inl a) (Sum.inr b) := by
-- proof
  apply StatMech.FK.fsm_not_reach_inl_inr G H a b

/--
[fsm_edgeSet_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_edgeSet_sum_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  (G ⊕g H).edgeSet = (Sym2.map Sum.inl '' G.edgeSet) ∪ (Sym2.map Sum.inr '' H.edgeSet) := by
-- proof
  apply StatMech.FK.fsm_edgeSet_sum

/--
[fsm_edgeFinset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_edgeFinset_sum_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  (G ⊕g H).edgeFinset = (G.edgeFinset.image (Sym2.map Sum.inl)) ∪ (H.edgeFinset.image (Sym2.map Sum.inr)) := by
-- proof
  apply StatMech.FK.fsm_edgeFinset_sum

/--
[fsm_map_inl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_map_inl_injective_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  Function.Injective (Sym2.map (Sum.inl : V → V ⊕ W)) := by
-- proof
  apply StatMech.FK.fsm_map_inl_injective

/--
[fsm_map_inr_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_map_inr_injective_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  Function.Injective (Sym2.map (Sum.inr : W → V ⊕ W)) := by
-- proof
  apply StatMech.FK.fsm_map_inr_injective

/--
[fsm_images_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_images_disjoint_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  Disjoint (G.edgeFinset.image (Sym2.map (Sum.inl : V → V ⊕ W))) (H.edgeFinset.image (Sym2.map (Sum.inr : W → V ⊕ W))) := by
-- proof
  apply StatMech.FK.fsm_images_disjoint

/--
[fsm_combine_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_combine_inl_eq
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
  {a b : V} :
-- imply
  fsm_combine σ τ s(Sum.inl a, Sum.inl b) = σ s(a, b) := by
-- proof
  apply StatMech.FK.fsm_combine_inl σ τ a b

/--
[fsm_combine_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_combine_inr_eq
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
  {a b : W} :
-- imply
  fsm_combine σ τ s(Sum.inr a, Sum.inr b) = τ s(a, b) := by
-- proof
  apply StatMech.FK.fsm_combine_inr σ τ a b

/--
[fsm_combine_map_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_combine_map_inl_eq
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
  {e : Sym2 V} :
-- imply
  fsm_combine σ τ (Sym2.map Sum.inl e) = σ e := by
-- proof
  apply StatMech.FK.fsm_combine_map_inl σ τ e

/--
[fsm_combine_map_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_combine_map_inr_eq
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
  {e : Sym2 W} :
-- imply
  fsm_combine σ τ (Sym2.map Sum.inr e) = τ e := by
-- proof
  apply StatMech.FK.fsm_combine_map_inr σ τ e

/--
[fsm_combine_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_combine_injective_eq :
-- imply
  Function.Injective fun p : (Sym2 V → Bool) × (Sym2 W → Bool) => fsm_combine p.1 p.2 := by
-- proof
  apply StatMech.FK.fsm_combine_injective

/--
[fsm_edgeProduct_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_edgeProduct_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p : ℝ}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool} :
-- imply
  edgeProduct (G ⊕g H) p (fsm_combine σ τ) = edgeProduct G p σ * edgeProduct H p τ := by
-- proof
  apply StatMech.FK.fsm_edgeProduct_combine p σ τ

/--
[fsm_openSub_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_openSub_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool} :
-- imply
  openSub (G ⊕g H) (fsm_combine σ τ) = (openSub G σ) ⊕g (openSub H τ) := by
-- proof
  apply StatMech.FK.fsm_openSub_combine σ τ

/--
[fsm_numClusters_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_numClusters_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool} :
-- imply
  numClusters (G ⊕g H) (fsm_combine σ τ) = numClusters G σ + numClusters H τ := by
-- proof
  apply StatMech.FK.fsm_numClusters_combine σ τ

/--
[fsm_fkWeight_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_fkWeight_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool} :
-- imply
  fkWeight (G ⊕g H) p q (fsm_combine σ τ) = fkWeight G p q σ * fkWeight H p q τ := by
-- proof
  apply StatMech.FK.fsm_fkWeight_combine p q σ τ

/--
[fsm_fkZ_sum_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_fkZ_sum_ge_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  fkZ G p q * fkZ H p q ≤ fkZ (G ⊕g H) p q := by
-- proof
  apply StatMech.FK.fsm_fkZ_sum_ge hp hp1 hq

/--
[fsm_neglog_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_neglog_sum_le_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  - Real.log (fkZ (G ⊕g H) p q) ≤ - Real.log (fkZ G p q) + - Real.log (fkZ H p q) := by
-- proof
  apply StatMech.FK.fsm_neglog_sum_le hp hp1 hq

/--
[fsm_numClusters_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_numClusters_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H}
  {ω : Sym2 W → Bool} :
-- imply
  numClusters G (fun e => ω (Sym2.map φ.toEquiv e)) = numClusters H ω := by
-- proof
  apply StatMech.FK.fsm_numClusters_iso φ ω

/--
[fsm_edgeProduct_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_edgeProduct_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H}
  {p : ℝ}
  {ω : Sym2 W → Bool} :
-- imply
  edgeProduct G p (fun e => ω (Sym2.map φ.toEquiv e)) = edgeProduct H p ω := by
-- proof
  apply StatMech.FK.fsm_edgeProduct_iso φ p ω

/--
[fsm_fkZ_iso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_fkZ_iso_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {φ : G ≃g H}
  {p q : ℝ} :
-- imply
  fkZ G p q = fkZ H p q := by
-- proof
  apply StatMech.FK.fsm_fkZ_iso φ p q

/--
[fsm_subadditive_neglog_fkZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_subadditive_neglog_fkZ_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n) :
-- imply
  Subadditive (fun n => - Real.log (fkZ (Gn n) p q)) := by
-- proof
  apply StatMech.FK.fsm_subadditive_neglog_fkZ hp hp1 hq hjux

/--
[fsm_fekete_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_fekete_limit_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  {q : ℝ}
  {c : ℝ → ℝ}
-- given
  (hq : 0 < q)
  (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
  (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
  (hbdd : ∀ t, BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
  (hc : ∀ t, c t ≠ 0)
  (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
-- imply
  ∃ g : ℝ → ℝ, (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (g t))) ∧ ConvexOn ℝ Set.univ g := by
-- proof
  apply StatMech.FK.fsm_fekete_limit q hq hE hjux hbdd c hc he

/--
[fsm_juxtaposition_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean)
-/
@[path]
private lemma fsm_juxtaposition_satisfiable_eq
  {m n : ℕ} :
-- imply
  Nonempty ((⊥ : SimpleGraph (Fin (m + n))) ≃g (⊥ : SimpleGraph (Fin m)) ⊕g (⊥ : SimpleGraph (Fin n))) := by
-- proof
  apply StatMech.FK.fsm_juxtaposition_satisfiable m n


-- created on 2026-10-23

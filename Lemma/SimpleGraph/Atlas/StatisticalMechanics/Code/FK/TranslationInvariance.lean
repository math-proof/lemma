import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fkTI_reCfg_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_reCfg_apply_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V ≃ V}
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V} :
-- imply
  reCfg σ ω e = ω (Sym2.map σ e) := by
-- proof
  apply StatMech.FK.fkTI_reCfg_apply σ ω e

/--
[fkTI_reCfg_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_reCfg_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V ≃ V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  reCfg σ.symm (reCfg σ ω) = ω := by
-- proof
  apply StatMech.FK.fkTI_reCfg_reCfg σ ω

/--
[fkTI_reCfg_reCfg'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_reCfg_reCfg'_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V ≃ V}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  reCfg σ (reCfg σ.symm ω) = ω := by
-- proof
  apply StatMech.FK.fkTI_reCfg_reCfg' σ ω

/--
[fkTI_numClusters_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_numClusters_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  numClusters G (reCfg σ ω) = numClusters G ω := by
-- proof
  apply StatMech.FK.fkTI_numClusters_reCfg G σ hσ ω

/--
[fkTI_mem_edgeFinset_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_mem_edgeFinset_map_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {e : Sym2 V}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (he : e ∈ G.edgeFinset) :
-- imply
  Sym2.map σ e ∈ G.edgeFinset := by
-- proof
  apply StatMech.FK.fkTI_mem_edgeFinset_map G σ hσ he

/--
[fkTI_mem_edgeFinset_map_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_mem_edgeFinset_map_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {e : Sym2 V}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (he : e ∈ G.edgeFinset) :
-- imply
  Sym2.map σ.symm e ∈ G.edgeFinset := by
-- proof
  apply StatMech.FK.fkTI_mem_edgeFinset_map_symm G σ hσ he

/--
[fkTI_edgeProduct_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_edgeProduct_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  edgeProduct G p (reCfg σ ω) = edgeProduct G p ω := by
-- proof
  apply StatMech.FK.fkTI_edgeProduct_reCfg G σ hσ p ω

/--
[fkTI_fkWeight_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_fkWeight_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  fkWeight G p q (reCfg σ ω) = fkWeight G p q ω := by
-- proof
  apply StatMech.FK.fkTI_fkWeight_reCfg G σ hσ p q ω

/--
[fkTI_fkZ_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_fkZ_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {p q : ℝ}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  fkZ G p q = ∑ ω : ConfigSpace (Sym2 V), fkWeight G p q (reCfg σ ω) := by
-- proof
  apply StatMech.FK.fkTI_fkZ_reCfg G σ hσ p q

/--
[fkTI_fkProb_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_fkProb_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {σ : V ≃ V}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  fkProb G p q (reCfg σ ω) = fkProb G p q ω := by
-- proof
  apply StatMech.FK.fkTI_fkProb_reCfg G σ hσ p q ω

/--
[fkTI_numClustersWired_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_numClustersWired_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (hbdry : ∀ x, bdry (σ x) ↔ bdry x) :
-- imply
  StatMech.Lattice.numClustersWired G bdry (reCfg σ ω) = StatMech.Lattice.numClustersWired G bdry ω := by
-- proof
  apply StatMech.FK.fkTI_numClustersWired_reCfg G bdry σ hσ hbdry ω

/--
[fkTI_wiredFkWeight_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_wiredFkWeight_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (hbdry : ∀ x, bdry (σ x) ↔ bdry x) :
-- imply
  wiredFkWeight G bdry p q (reCfg σ ω) = wiredFkWeight G bdry p q ω := by
-- proof
  apply StatMech.FK.fkTI_wiredFkWeight_reCfg G bdry σ hσ hbdry p q ω

/--
[fkTI_wiredFkProb_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_wiredFkProb_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop)
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (hbdry : ∀ x, bdry (σ x) ↔ bdry x) :
-- imply
  wiredFkProb G bdry p q (reCfg σ ω) = wiredFkProb G bdry p q ω := by
-- proof
  apply StatMech.FK.fkTI_wiredFkProb_reCfg G bdry σ hσ hbdry p q ω

/--
[fkTI_edgeMargProb_reCfg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_edgeMargProb_reCfg_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {μ : ConfigSpace (Sym2 V) → ℝ}
  {e : Sym2 V}
-- given
  (bdry : V → Prop)
  (hμ : ∀ ω, μ (reCfg σ.symm ω) = μ ω) :
-- imply
  edgeMargProb μ (Sym2.map σ e) = edgeMargProb μ e := by
-- proof
  apply StatMech.FK.fkTI_edgeMargProb_reCfg_inv G bdry σ μ hμ e

/--
[fkTI_edgeMargProb_fkProb_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_edgeMargProb_fkProb_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdry : V → Prop)
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y) :
-- imply
  edgeMargProb (fkProb G p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e := by
-- proof
  apply StatMech.FK.fkTI_edgeMargProb_fkProb_reCfg G bdry σ hσ p q e

/--
[fkTI_edgeMargProb_wiredFkProb_reCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_edgeMargProb_wiredFkProb_reCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {σ : V ≃ V}
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdry : V → Prop)
  (hσ : ∀ x y, G.Adj (σ x) (σ y) ↔ G.Adj x y)
  (hbdry : ∀ x, bdry (σ x) ↔ bdry x) :
-- imply
  edgeMargProb (wiredFkProb G bdry p q) (Sym2.map σ e) = edgeMargProb (wiredFkProb G bdry p q) e := by
-- proof
  apply StatMech.FK.fkTI_edgeMargProb_wiredFkProb_reCfg G bdry σ hσ hbdry p q e

/--
[BoxSym.lift_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma lift_val_eq
  {d : ℕ}
  {S : BoxSym d}
  {n : ℕ}
  {x : boxVerts d n} :
-- imply
  (S.lift n x : Site d) = S.τ x.val := by
-- proof
  apply StatMech.FK.BoxSym.lift_val S n x

/--
[BoxSym.lift_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma lift_adj_eq
  {d : ℕ}
  {S : BoxSym d}
  {n : ℕ}
  {x y : boxVerts d n} :
-- imply
  (boxGraph d n).Adj (S.lift n x) (S.lift n y) ↔ (boxGraph d n).Adj x y := by
-- proof
  apply StatMech.FK.BoxSym.lift_adj S n x y

/--
[BoxSym.lift_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma lift_boundary_eq
  {d : ℕ}
  {S : BoxSym d}
  {n : ℕ}
  {x : boxVerts d n} :
-- imply
  boxBoundary d n (S.lift n x) ↔ boxBoundary d n x := by
-- proof
  apply StatMech.FK.BoxSym.lift_boundary S n x

/--
[BoxSym.lift_boxVertInclLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma lift_boxVertInclLE_eq
  {d : ℕ}
  {S : BoxSym d}
  {N m : ℕ}
  {x : boxVerts d N}
-- given
  (h : N ≤ m) :
-- imply
  S.lift m (boxVertInclLE d h x) = boxVertInclLE d h (S.lift N x) := by
-- proof
  apply StatMech.FK.BoxSym.lift_boxVertInclLE S h x

/--
[BoxSym.lift_innerEdgeLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma lift_innerEdgeLE_eq
  {d : ℕ}
  {S : BoxSym d}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (h : N ≤ m) :
-- imply
  Sym2.map (S.lift m) (innerEdgeLE d h eb) = innerEdgeLE d h (Sym2.map (S.lift N) eb) := by
-- proof
  apply StatMech.FK.BoxSym.lift_innerEdgeLE S h eb

/--
[fkTI_box_wired_edgeMarg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_box_wired_edgeMarg_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {m : ℕ}
  {p : ℝ}
  {e : Sym2 (boxVerts d m)} :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (Sym2.map (S.lift m) e) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e := by
-- proof
  apply StatMech.FK.fkTI_box_wired_edgeMarg_inv S m e

/--
[fkTI_box_free_edgeMarg_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_box_free_edgeMarg_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {m : ℕ}
  {p : ℝ}
  {e : Sym2 (boxVerts d m)} :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p 2) (Sym2.map (S.lift m) e) = edgeMargProb (fkProb (boxGraph d m) p 2) e := by
-- proof
  apply StatMech.FK.fkTI_box_free_edgeMarg_inv S m e

/--
[fkTI_wired_density_shift_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_wired_density_shift_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fkTI_wired_density_shift_inv S N eb hp hp1

/--
[fkTI_free_density_shift_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_free_density_shift_inv_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fkTI_free_density_shift_inv S N eb hp hp1

/--
[fkTI_signFlip_moves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_signFlip_moves_eq
  {d : ℕ}
  {d : ℕ}
  {j : Fin d}
  {x : Site d}
-- given
  (hx : x j ≠ 0) :
-- imply
  (fkTI_signFlip d j).τ x ≠ x := by
-- proof
  apply StatMech.FK.fkTI_signFlip_moves d j x hx

/--
[fkTI_box_density_bound_wired_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_box_density_bound_wired_const_eq
  {d : ℕ}
  {S : BoxSym d}
  {N n : ℕ}
  {EB₀ : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hconst : ∀ eb ∈ EB₀, wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (EB₀.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.fkTI_box_density_bound_wired_const S N n hNn EB₀ eb₀ hconst hp hp1

/--
[fkTI_box_density_bound_free_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean)
-/
@[path]
private lemma fkTI_box_density_bound_free_const_eq
  {d : ℕ}
  {S : BoxSym d}
  {N n : ℕ}
  {EB₀ : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hconst : ∀ eb ∈ EB₀, freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω * fkProb (boxGraph d n) p 2 ω) ≤ (EB₀.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
-- proof
  apply StatMech.FK.fkTI_box_density_bound_free_const S N n hNn EB₀ eb₀ hconst hp hp1


-- created on 2026-10-23

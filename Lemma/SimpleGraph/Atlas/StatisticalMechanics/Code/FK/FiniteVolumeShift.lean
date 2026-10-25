import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fvs_reCfgIso_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_reCfgIso_apply_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace (Sym2 W)}
  {e : Sym2 V} :
-- imply
  reCfgIso σ ω e = ω (Sym2.map σ e) := by
-- proof
  apply StatMech.FK.fvs_reCfgIso_apply σ ω e

/--
[fvs_reCfgIso_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_reCfgIso_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace (Sym2 W)} :
-- imply
  reCfgIso σ.symm (reCfgIso σ ω) = ω := by
-- proof
  apply StatMech.FK.fvs_reCfgIso_reCfgIso σ ω

/--
[fvs_reCfgIso_reCfgIso'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_reCfgIso_reCfgIso'_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  reCfgIso σ (reCfgIso σ.symm ω) = ω := by
-- proof
  apply StatMech.FK.fvs_reCfgIso_reCfgIso' σ ω

/--
[fvs_numClusters_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_numClusters_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  numClusters G (reCfgIso σ ω) = numClusters H ω := by
-- proof
  apply StatMech.FK.fvs_numClusters_reCfgIso G H σ hσ ω

/--
[fvs_mem_edgeFinset_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_mem_edgeFinset_map_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {e : Sym2 V}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (he : e ∈ G.edgeFinset) :
-- imply
  Sym2.map σ e ∈ H.edgeFinset := by
-- proof
  apply StatMech.FK.fvs_mem_edgeFinset_map G H σ hσ he

/--
[fvs_mem_edgeFinset_map_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_mem_edgeFinset_map_symm_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {e : Sym2 W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (he : e ∈ H.edgeFinset) :
-- imply
  Sym2.map σ.symm e ∈ G.edgeFinset := by
-- proof
  apply StatMech.FK.fvs_mem_edgeFinset_map_symm G H σ hσ he

/--
[fvs_edgeProduct_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_edgeProduct_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {p : ℝ}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  edgeProduct G p (reCfgIso σ ω) = edgeProduct H p ω := by
-- proof
  apply StatMech.FK.fvs_edgeProduct_reCfgIso G H σ hσ p ω

/--
[fvs_fkWeight_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_fkWeight_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  fkWeight G p q (reCfgIso σ ω) = fkWeight H p q ω := by
-- proof
  apply StatMech.FK.fvs_fkWeight_reCfgIso G H σ hσ p q ω

/--
[fvs_fkZ_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_fkZ_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {p q : ℝ}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  fkZ G p q = fkZ H p q := by
-- proof
  apply StatMech.FK.fvs_fkZ_reCfgIso G H σ hσ p q

/--
[fvs_fkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_fkProb_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  fkProb G p q (reCfgIso σ ω) = fkProb H p q ω := by
-- proof
  apply StatMech.FK.fvs_fkProb_reCfgIso G H σ hσ p q ω

/--
[fvs_numClustersWired_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_numClustersWired_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  StatMech.Lattice.numClustersWired G bdryV (reCfgIso σ ω) = StatMech.Lattice.numClustersWired H bdryW ω := by
-- proof
  apply StatMech.FK.fvs_numClustersWired_reCfgIso G H bdryV bdryW σ hσ hbdry ω

/--
[fvs_wiredFkWeight_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_wiredFkWeight_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  wiredFkWeight G bdryV p q (reCfgIso σ ω) = wiredFkWeight H bdryW p q ω := by
-- proof
  apply StatMech.FK.fvs_wiredFkWeight_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω

/--
[fvs_wiredFkZ_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_wiredFkZ_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  wiredFkZ G bdryV p q = wiredFkZ H bdryW p q := by
-- proof
  apply StatMech.FK.fvs_wiredFkZ_reCfgIso G H bdryV bdryW σ hσ hbdry p q

/--
[fvs_wiredFkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_wiredFkProb_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 W)}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  wiredFkProb G bdryV p q (reCfgIso σ ω) = wiredFkProb H bdryW p q ω := by
-- proof
  apply StatMech.FK.fvs_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q ω

/--
[fvs_edgeMargProb_reCfgIso_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_edgeMargProb_reCfgIso_inv_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {μV : ConfigSpace (Sym2 V) → ℝ}
  {μW : ConfigSpace (Sym2 W) → ℝ}
  {e : Sym2 V}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hμ : ∀ ω, μV (reCfgIso σ ω) = μW ω) :
-- imply
  edgeMargProb μW (Sym2.map σ e) = edgeMargProb μV e := by
-- proof
  apply StatMech.FK.fvs_edgeMargProb_reCfgIso_inv G H bdryV bdryW σ μV μW hμ e

/--
[fvs_edgeMargProb_fkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_edgeMargProb_fkProb_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e := by
-- proof
  apply StatMech.FK.fvs_edgeMargProb_fkProb_reCfgIso G H bdryV bdryW σ hσ p q e

/--
[fvs_edgeMargProb_wiredFkProb_reCfgIso](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_edgeMargProb_wiredFkProb_reCfgIso_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e) = edgeMargProb (wiredFkProb G bdryV p q) e := by
-- proof
  apply StatMech.FK.fvs_edgeMargProb_wiredFkProb_reCfgIso G H bdryV bdryW σ hσ hbdry p q e

/--
[fvs_finiteVolume_shift_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_finiteVolume_shift_invariant_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  [DecidablePred bdryV]
  [DecidablePred bdryW]
  {σ : V ≃ W}
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (bdryV : V → Prop)
  (bdryW : W → Prop)
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (hbdry : ∀ x, bdryV x ↔ bdryW (σ x)) :
-- imply
  edgeMargProb (wiredFkProb H bdryW p q) (Sym2.map σ e) = edgeMargProb (wiredFkProb G bdryV p q) e ∧ edgeMargProb (fkProb H p q) (Sym2.map σ e) = edgeMargProb (fkProb G p q) e := by
-- proof
  apply StatMech.FK.fvs_finiteVolume_shift_invariant G H bdryV bdryW σ hσ hbdry p q e

/--
[fvs_transEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_transEquiv_val_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {x : boxVerts d m} :
-- imply
  (fvs_transEquiv d m v x : Site d) = (x : Site d) + v := by
-- proof
  apply StatMech.FK.fvs_transEquiv_val d m v x

/--
[fvs_transEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_transEquiv_adj_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {x y : boxVerts d m} :
-- imply
  (boxGraph d m).Adj x y ↔ (fvs_transBoxGraph d m v).Adj (fvs_transEquiv d m v x) (fvs_transEquiv d m v y) := by
-- proof
  apply StatMech.FK.fvs_transEquiv_adj d m v x y

/--
[fvs_transEquiv_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_transEquiv_boundary_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {x : boxVerts d m} :
-- imply
  boxBoundary d m x ↔ fvs_transBoxBoundary d m v (fvs_transEquiv d m v x) := by
-- proof
  apply StatMech.FK.fvs_transEquiv_boundary d m v x

/--
[fvs_box_translation_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_box_translation_edgeMarg_eq
  {d : ℕ}
  {d m : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d m)}
  {p q : ℝ} :
-- imply
  edgeMargProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) eb ∧ edgeMargProb (fkProb (fvs_transBoxGraph d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb) = edgeMargProb (fkProb (boxGraph d m) p q) eb := by
-- proof
  apply StatMech.FK.fvs_box_translation_edgeMarg d m v eb

/--
[fvs_transBox_ne_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteVolumeShift.lean)
-/
@[path]
private lemma fvs_transBox_ne_box_eq
  {d : ℕ}
  {d m : ℕ}
-- given
  (hd : 0 < d) :
-- imply
  ∃ (v y : Site d), y ∈ fvs_transBox d m v ∧ y ∉ box d m := by
-- proof
  apply StatMech.FK.fvs_transBox_ne_box d m hd


-- created on 2026-10-23

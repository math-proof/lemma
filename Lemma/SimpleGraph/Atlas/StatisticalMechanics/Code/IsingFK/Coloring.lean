import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
open StatMech StatMech.IsingFK


/--
[compatible_iff_constOnOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma compatible_iff_constOnOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  Compatible G σ ω ↔ ConstOnOpen G ω σ := by
-- proof
  apply StatMech.IsingFK.compatible_iff_constOnOpen G σ ω

/--
[compatible_constant_on_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma compatible_constant_on_cluster_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {x y : V}
  {r : (openSub G ω).Reachable x y}
-- given
  (h : Compatible G σ ω) :
-- imply
  σ x = σ y := by
-- proof
  apply StatMech.IsingFK.compatible_constant_on_cluster G σ ω h r

/--
[monoBool_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma monoBool_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {x y : V} :
-- imply
  monoBool σ s(x, y) = decide (σ x = σ y) := by
-- proof
  apply StatMech.IsingFK.monoBool_mk G σ x y

/--
[monoBool_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma monoBool_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {x y : V} :
-- imply
  monoBool σ s(x, y) = true ↔ σ x = σ y := by
-- proof
  apply StatMech.IsingFK.monoBool_iff G σ x y

/--
[mem_disagreeEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma mem_disagreeEdges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {x y : V} :
-- imply
  s(x, y) ∈ disagreeEdges G σ ↔ G.Adj x y ∧ σ x ≠ σ y := by
-- proof
  apply StatMech.IsingFK.mem_disagreeEdges G σ x y

/--
[compatible_closed_on_disagree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma compatible_closed_on_disagree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
  {e : Sym2 V}
-- given
  (h : Compatible G σ ω)
  (he : e ∈ disagreeEdges G σ) :
-- imply
  ω e = false := by
-- proof
  apply StatMech.IsingFK.compatible_closed_on_disagree G σ ω h he

/--
[coloring_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma coloring_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {τ : (openSub G ω).ConnectedComponent → Fin q}
  {x : V} :
-- imply
  coloring G ω τ x = τ ((openSub G ω).connectedComponentMk x) := by
-- proof
  apply StatMech.IsingFK.coloring_apply G ω τ x

/--
[coloring_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma coloring_compatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {τ : (openSub G ω).ConnectedComponent → Fin q} :
-- imply
  Compatible G (coloring G ω τ) ω := by
-- proof
  apply StatMech.IsingFK.coloring_compatible G ω τ

/--
[coloring_eq_constOnOpenEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma coloring_eq_constOnOpenEquiv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)}
  {τ : (openSub G ω).ConnectedComponent → Fin q} :
-- imply
  coloring G ω τ = (constOnOpenEquiv G ω τ).1 := by
-- proof
  apply StatMech.IsingFK.coloring_eq_constOnOpenEquiv G ω τ

/--
[card_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma card_compatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  Nat.card {σ : V → Fin q // Compatible G σ ω} = q ^ numClusters G ω := by
-- proof
  apply StatMech.IsingFK.card_compatible G ω

/--
[edgeProduct_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma edgeProduct_eq_pow_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProduct G p ω = p ^ openCount G ω * (1 - p) ^ closedCount G ω := by
-- proof
  apply StatMech.IsingFK.edgeProduct_eq_pow G p ω

/--
[esWeight_eq_of_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma esWeight_eq_of_compatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esWeight G p σ ω = if Compatible G σ ω then edgeProduct G p ω else 0 := by
-- proof
  apply StatMech.IsingFK.esWeight_eq_of_compatible G p σ ω

/--
[esJointProb_incompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma esJointProb_incompatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (h : ¬ Compatible G σ ω) :
-- imply
  esJointProb G q p σ ω = 0 := by
-- proof
  apply StatMech.IsingFK.esJointProb_incompatible G p σ ω h

/--
[esJointProb_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma esJointProb_compatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (h : Compatible G σ ω) :
-- imply
  esJointProb G q p σ ω = (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ) := by
-- proof
  apply StatMech.IsingFK.esJointProb_compatible G p σ ω h

/--
[esJointProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean)
-/
@[path]
private lemma esJointProb_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {q : ℕ}
  {p : ℝ}
  {σ : V → Fin q}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  esJointProb G q p σ ω = if Compatible G σ ω then (p ^ openCount G ω * (1 - p) ^ closedCount G ω) / fkZ G p (q : ℝ) else 0 := by
-- proof
  apply StatMech.IsingFK.esJointProb_eq G p σ ω


-- created on 2026-10-23

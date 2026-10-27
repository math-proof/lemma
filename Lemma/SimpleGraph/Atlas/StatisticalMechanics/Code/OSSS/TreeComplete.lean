import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.TreeComplete.Part5
open Finset StatMech.Lattice StatMech StatMech.OSSS StatMech.OSSS.TreeComplete


/--
[subset_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma subset_runState_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {disc : Finset V} :
-- imply
  disc ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
-- proof
  apply StatMech.OSSS.TreeComplete.subset_runState endU endV ω l disc

/--
[subset_geomStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma subset_geomStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {disc : Finset V}
  {e : E}
  {b : Bool} :
-- imply
  disc ⊆ geomStep endU endV disc e b := by
-- proof
  apply StatMech.OSSS.TreeComplete.subset_geomStep endU endV disc e b

/--
[runState_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma runState_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {d₁ d₂ : Finset V}
-- given
  (h : d₁ ⊆ d₂) :
-- imply
  runState (geomGuard endU endV) (geomStep endU endV) ω l d₁ ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l d₂ := by
-- proof
  apply StatMech.OSSS.TreeComplete.runState_mono endU endV ω l h

/--
[mem_runState_of_open_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma mem_runState_of_open_edge_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {disc : Finset V}
  {e : E}
-- given
  (he : e ∈ l)
  (hopen : ω e = true)
  (hend : endU e ∈ disc ∨ endV e ∈ disc) :
-- imply
  endU e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc ∧ endV e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
-- proof
  apply StatMech.OSSS.TreeComplete.mem_runState_of_open_edge endU endV ω l disc e he hopen hend

/--
[runState_subset_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma runState_subset_union_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {disc : Finset V} :
-- imply
  runState (geomGuard endU endV) (geomStep endU endV) ω l disc ⊆ disc ∪ endpointsFinset endU endV l := by
-- proof
  apply StatMech.OSSS.TreeComplete.runState_subset_union endU endV ω l disc

/--
[mem_of_reachOpen_of_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma mem_of_reachOpen_of_saturated_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {D : Finset V}
  {x b : V}
-- given
  (hsat : Saturated endU endV ω l D)
  (hl : ∀ e, e ∈ l)
  (h : ReachOpen endU endV ω x b)
  (hb : b ∈ D) :
-- imply
  x ∈ D := by
-- proof
  apply StatMech.OSSS.TreeComplete.mem_of_reachOpen_of_saturated endU endV ω l D hsat hl h hb

/--
[saturated_of_fixpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma saturated_of_fixpoint_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {D : Finset V}
-- given
  (hfix : runState (geomGuard endU endV) (geomStep endU endV) ω l D = D) :
-- imply
  Saturated endU endV ω l D := by
-- proof
  apply StatMech.OSSS.TreeComplete.saturated_of_fixpoint endU endV ω l D hfix

/--
[runState_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma runState_append_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l₁ l₂ : List E}
  {disc : Finset V} :
-- imply
  runState (geomGuard endU endV) (geomStep endU endV) ω (l₁ ++ l₂) disc = runState (geomGuard endU endV) (geomStep endU endV) ω l₂ (runState (geomGuard endU endV) (geomStep endU endV) ω l₁ disc) := by
-- proof
  apply StatMech.OSSS.TreeComplete.runState_append endU endV ω l₁ l₂ disc

/--
[runState_repeatList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma runState_repeatList_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {n : ℕ}
  {disc : Finset V} :
-- imply
  runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l n) disc = (fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D)^[n] disc := by
-- proof
  apply StatMech.OSSS.TreeComplete.runState_repeatList endU endV ω l n disc

/--
[fixpoint_iterate_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma fixpoint_iterate_card_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [DecidableEq V]
  {f : Finset V → Finset V}
  {U : Finset V}
  {D₀ : Finset V}
-- given
  (hinfl : ∀ D, D ⊆ f D)
  (hbound : ∀ D, D ⊆ U → f D ⊆ U)
  (hD₀ : D₀ ⊆ U) :
-- imply
  f (f^[U.card] D₀) = f^[U.card] D₀ := by
-- proof
  apply StatMech.OSSS.TreeComplete.fixpoint_iterate_card f U hinfl hbound D₀ hD₀

/--
[runState_repeatList_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma runState_repeatList_saturated_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {disc₀ : Finset V} :
-- imply
  Saturated endU endV ω l (runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀) := by
-- proof
  apply StatMech.OSSS.TreeComplete.runState_repeatList_saturated endU endV ω l disc₀

/--
[mem_runState_repeatList_of_connOpenSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma mem_runState_repeatList_of_connOpenSet_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {l : List E}
  {B : Set V}
  {disc₀ : Finset V}
  {o : V}
-- given
  (hl : ∀ e, e ∈ l)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀)
  (h : ConnOpenSet endU endV ω o B) :
-- imply
  o ∈ runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀ := by
-- proof
  apply StatMech.OSSS.TreeComplete.mem_runState_repeatList_of_connOpenSet endU endV ω l hl B disc₀ hBdisc h

/--
[eval_completeTree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma eval_completeTree_iff_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
-- given
  (hl : ∀ e, e ∈ l)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀) :
-- imply
  (completeTree endU endV o l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o B := by
-- proof
  apply StatMech.OSSS.TreeComplete.eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω

/--
[evalR_completeTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma evalR_completeTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  [Decidable (ConnOpenSet endU endV ω o B)]
-- given
  (hl : ∀ e, e ∈ l)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀) :
-- imply
  (completeTree endU endV o l disc₀).evalR ω = if ConnOpenSet endU endV ω o B then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.TreeComplete.evalR_completeTree endU endV o B l hl disc₀ hdisc₀ hBdisc ω

/--
[exists_abstract_open_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma exists_abstract_open_edge_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {u v : Site d}
-- given
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hopen : liftCfg edge ω s(u, v) = true) :
-- imply
  ∃ e, ω e = true ∧ ((endU e = u ∧ endV e = v) ∨ (endU e = v ∧ endV e = u)) := by
-- proof
  apply StatMech.OSSS.TreeComplete.exists_abstract_open_edge hcoh hopen

/--
[connected_imp_reachOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma connected_imp_reachOpen_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {x y : Site d}
-- given
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (h : Connected d (liftCfg edge ω) x y) :
-- imply
  ReachOpen endU endV ω x y := by
-- proof
  apply StatMech.OSSS.TreeComplete.connected_imp_reachOpen hcoh h

/--
[connectedToSet_imp_connOpenSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma connectedToSet_imp_connOpenSet_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {x : Site d}
  {B : Set (Site d)}
-- given
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (h : ConnectedToSet d (liftCfg edge ω) x B) :
-- imply
  ConnOpenSet endU endV ω x B := by
-- proof
  apply StatMech.OSSS.TreeComplete.connectedToSet_imp_connOpenSet hcoh h

/--
[evalR_completeTree_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/TreeComplete.lean)
-/
@[path]
private lemma evalR_completeTree_connected_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {B : Set (Site d)}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {ω : ConfigSpace E}
  [Decidable (ConnectedToSet d (liftCfg edge ω) o B)]
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hl : ∀ e, e ∈ l)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀) :
-- imply
  (completeTree endU endV o l disc₀).evalR ω = if ConnectedToSet d (liftCfg edge ω) o B then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.TreeComplete.evalR_completeTree_connected hinj hcoh hadj o B l hl disc₀ hdisc₀ hBdisc ω


-- created on 2026-10-23

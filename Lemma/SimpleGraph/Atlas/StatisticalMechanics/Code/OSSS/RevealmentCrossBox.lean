import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
open Finset StatMech.Lattice StatMech StatMech.OSSS


/--
[reachOpen_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reachOpen_symm_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {x y : V}
-- given
  (h : ReachOpen endU endV ω x y) :
-- imply
  ReachOpen endU endV ω y x := by
-- proof
  apply StatMech.OSSS.reachOpen_symm h

/--
[cb_adj_coord_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma cb_adj_coord_le_one_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {x y : Site d}
  {i : Fin d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  (x i - y i).natAbs ≤ 1 := by
-- proof
  apply StatMech.OSSS.cb_adj_coord_le_one d x y hadj i

/--
[cb_mem_box_of_adj_box_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma cb_mem_box_of_adj_box_pred_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d k : ℕ}
  {x y : Site d}
-- given
  (hk : 1 ≤ k)
  (hx : x ∈ box d (k - 1))
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  y ∈ box d k := by
-- proof
  apply StatMech.OSSS.cb_mem_box_of_adj_box_pred d k hk x y hx hadj

/--
[reachOpen_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reachOpen_crosses_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d k : ℕ}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {o b : Site d}
-- given
  (hk : 1 ≤ k)
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (h : ReachOpen endU endV ω o b)
  (ho : o ∈ box d (k - 1))
  (hb : b ∉ box d (k - 1)) :
-- imply
  ConnOpenSet endU endV ω o (vertexBoundary d k) := by
-- proof
  apply StatMech.OSSS.reachOpen_crosses hk hadj h ho hb

/--
[connOpenSet_boundary_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma connOpenSet_boundary_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d k n : ℕ}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {o : Site d}
-- given
  (hk : 1 ≤ k)
  (hkn : k ≤ n)
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (ho : o ∈ box d (k - 1))
  (h : ConnOpenSet endU endV ω o (vertexBoundary d n)) :
-- imply
  ConnOpenSet endU endV ω o (vertexBoundary d k) := by
-- proof
  apply StatMech.OSSS.connOpenSet_boundary_mono hk hkn hadj ho h

/--
[cb_not_mem_vertexBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma cb_not_mem_vertexBoundary_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d k n : ℕ}
  {o : Site d}
-- given
  (hkn : k ≤ n)
  (ho : o ∈ box d (k - 1)) :
-- imply
  o ∉ vertexBoundary d n := by
-- proof
  apply StatMech.OSSS.cb_not_mem_vertexBoundary hkn ho

/--
[fst_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma fst_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {s : XState V}
  {e : E}
  {b : Bool} :
-- imply
  (xbStep endU endV o s e b).1 = geomStep endU endV s.1 e b := by
-- proof
  apply StatMech.OSSS.fst_xbStep endU endV o s e b

/--
[snd_xbStep_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma snd_xbStep_eq_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {s : XState V}
  {e : E}
  {b : Bool} :
-- imply
  (xbStep endU endV o s e b).2 = (if o ∈ geomStep endU endV s.1 e b then insert o else id) (if b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2) then insert (endU e) (insert (endV e) s.2) else s.2) := by
-- proof
  apply StatMech.OSSS.snd_xbStep_eq endU endV o s e b

/--
[fst_runState_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma fst_runState_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V} :
-- imply
  (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1 = runState (geomGuard endU endV) (geomStep endU endV) ω l s.1 := by
-- proof
  apply StatMech.OSSS.fst_runState_xbStep endU endV o ω l s

/--
[subset_snd_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma subset_snd_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {s : XState V}
  {e : E}
  {b : Bool} :
-- imply
  s.2 ⊆ (xbStep endU endV o s e b).2 := by
-- proof
  apply StatMech.OSSS.subset_snd_xbStep endU endV o s e b

/--
[subset_snd_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma subset_snd_runState_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V} :
-- imply
  s.2 ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
-- proof
  apply StatMech.OSSS.subset_snd_runState endU endV o ω l s

/--
[snd_sub_fst_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma snd_sub_fst_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {s : XState V}
  {e : E}
  {b : Bool}
-- given
  (hs : s.2 ⊆ s.1) :
-- imply
  (xbStep endU endV o s e b).2 ⊆ (xbStep endU endV o s e b).1 := by
-- proof
  apply StatMech.OSSS.snd_sub_fst_xbStep endU endV o s e b hs

/--
[snd_sub_fst_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma snd_sub_fst_runState_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V}
-- given
  (hs : s.2 ⊆ s.1) :
-- imply
  (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1 := by
-- proof
  apply StatMech.OSSS.snd_sub_fst_runState endU endV o ω l s hs

/--
[reach0Inv_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reach0Inv_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {o : V}
  {s : XState V}
  {e : E}
-- given
  (hInv : reach0Inv endU endV ω o s) :
-- imply
  reach0Inv endU endV ω o (xbStep endU endV o s e (ω e)) := by
-- proof
  apply StatMech.OSSS.reach0Inv_xbStep endU endV ω o s e hInv

/--
[reach0Inv_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reach0Inv_runState_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {o : V}
  {l : List E}
  {s : XState V}
-- given
  (hInv : reach0Inv endU endV ω o s) :
-- imply
  reach0Inv endU endV ω o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
-- proof
  apply StatMech.OSSS.reach0Inv_runState endU endV ω o l s hInv

/--
[oSeedInv_xbStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma oSeedInv_xbStep_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {s : XState V}
  {e : E}
  {b : Bool} :
-- imply
  oSeedInv o (xbStep endU endV o s e b) := by
-- proof
  apply StatMech.OSSS.oSeedInv_xbStep endU endV o s e b

/--
[oSeedInv_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma oSeedInv_runState_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V}
-- given
  (hs : oSeedInv o s) :
-- imply
  oSeedInv o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
-- proof
  apply StatMech.OSSS.oSeedInv_runState endU endV o ω l s hs

/--
[mem_snd_runState_of_open_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma mem_snd_runState_of_open_edge_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V}
  {e : E}
-- given
  (hs : s.2 ⊆ s.1)
  (he : e ∈ l)
  (hopen : ω e = true)
  (hend : endU e ∈ s.2 ∨ endV e ∈ s.2) :
-- imply
  endU e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 ∧ endV e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
-- proof
  apply StatMech.OSSS.mem_snd_runState_of_open_edge endU endV o ω l s hs e he hopen hend

/--
[snd_saturated_of_fixpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma snd_saturated_of_fixpoint_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V}
-- given
  (hs : s.2 ⊆ s.1)
  (hfix : runState (xbGuard endU endV) (xbStep endU endV o) ω l s = s) :
-- imply
  Saturated endU endV ω l s.2 := by
-- proof
  apply StatMech.OSSS.snd_saturated_of_fixpoint endU endV o ω l s hs hfix

/--
[pairFixpoint_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma pairFixpoint_iterate_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  [DecidableEq W]
  {f : (Finset W × Finset W) → (Finset W × Finset W)}
  {U : Finset W}
  {s₀ : Finset W × Finset W}
-- given
  (hinfl1 : ∀ s, s.1 ⊆ (f s).1)
  (hinfl2 : ∀ s, s.2 ⊆ (f s).2)
  (hb1 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).1 ⊆ U)
  (hb2 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).2 ⊆ U)
  (h01 : s₀.1 ⊆ U)
  (h02 : s₀.2 ⊆ U) :
-- imply
  f (f^[2 * U.card] s₀) = f^[2 * U.card] s₀ := by
-- proof
  apply StatMech.OSSS.pairFixpoint_iterate f U hinfl1 hinfl2 hb1 hb2 s₀ h01 h02

/--
[runState_append_xb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma runState_append_xb_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l₁ l₂ : List E}
  {s : XState V} :
-- imply
  runState (xbGuard endU endV) (xbStep endU endV o) ω (l₁ ++ l₂) s = runState (xbGuard endU endV) (xbStep endU endV o) ω l₂ (runState (xbGuard endU endV) (xbStep endU endV o) ω l₁ s) := by
-- proof
  apply StatMech.OSSS.runState_append_xb endU endV o ω l₁ l₂ s

/--
[runState_repeatList_xb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma runState_repeatList_xb_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {n : ℕ}
  {s : XState V} :
-- imply
  runState (xbGuard endU endV) (xbStep endU endV o) ω (repeatList l n) s = (xbPass endU endV o ω l)^[n] s := by
-- proof
  apply StatMech.OSSS.runState_repeatList_xb endU endV o ω l n s

/--
[snd_runState_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma snd_runState_subset_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {s : XState V} :
-- imply
  (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 ⊆ s.2 ∪ endpointsFinset endU endV l ∪ {o} := by
-- proof
  apply StatMech.OSSS.snd_runState_subset endU endV o ω l s

/--
[xbPass_fixpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma xbPass_fixpoint_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {ω : ConfigSpace E}
  {l : List E}
  {disc₀ : Finset V} :
-- imply
  xbPass endU endV o ω l ((xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅)) = (xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅) := by
-- proof
  apply StatMech.OSSS.xbPass_fixpoint endU endV o ω l disc₀

/--
[eval_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma eval_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E} :
-- imply
  (crossTree endU endV o C l disc₀).eval ω = decide (∃ y ∈ ((xbPass endU endV o ω l)^[xbCount endU endV o l disc₀] (disc₀, ∅)).2, y ∈ C) := by
-- proof
  apply StatMech.OSSS.eval_crossTree endU endV o C l disc₀ ω

/--
[eval_crossTree_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma eval_crossTree_iff_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
-- given
  (hl : ∀ e, e ∈ l)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀)
  (hoB : o ∉ disc₀)
  (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B) :
-- imply
  (crossTree endU endV o C l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o C := by
-- proof
  apply StatMech.OSSS.eval_crossTree_iff endU endV o B C l hl disc₀ hBdisc hoB hcross ω

/--
[evalR_crossTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma evalR_crossTree_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  [Decidable (ConnOpenSet endU endV ω o C)]
-- given
  (hl : ∀ e, e ∈ l)
  (hBdisc : ∀ b ∈ B, b ∈ disc₀)
  (hoB : o ∉ disc₀)
  (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B) :
-- imply
  (crossTree endU endV o C l disc₀).evalR ω = if ConnOpenSet endU endV ω o C then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.evalR_crossTree endU endV o B C l hl disc₀ hBdisc hoB hcross ω

/--
[queried_crossTree_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma queried_crossTree_imp_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {ω : ConfigSpace E}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
-- imply
  ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
-- proof
  apply StatMech.OSSS.queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hi

/--
[reveal_crossTree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reveal_crossTree_le_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {ν : E → Bool → ℝ}
  {endU endV : E → V}
  {o : V}
  {B C : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  reveal ν (crossTree endU endV o C l disc₀) i ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0) + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.reveal_crossTree_le hν endU endV o B C l disc₀ hdisc₀ i

/--
[evalR_crossTree_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma evalR_crossTree_connected_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {k n : ℕ}
  {o : Site d}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {ω : ConfigSpace E}
  [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))]
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hk : 1 ≤ k)
  (hkn : k ≤ n)
  (ho : o ∈ box d (k - 1))
  (hl : ∀ e, e ∈ l)
  (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ disc₀)
  (hoB : o ∉ disc₀) :
-- imply
  (crossTree endU endV o (vertexBoundary d n) l disc₀).evalR ω = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.OSSS.evalR_crossTree_connected hinj hcoh hadj k n hk hkn o ho l hl disc₀ hBdisc hoB ω

/--
[reveal_crossTree_le_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentCrossBox.lean)
-/
@[path]
private lemma reveal_crossTree_le_connected_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {o : Site d}
  {C : Set (Site d)}
  {k : ℕ}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) :
-- imply
  reveal ν (crossTree endU endV o C l disc₀) i ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0) + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.reveal_crossTree_le_connected hν hinj hcoh hadj o C k l disc₀ hdisc₀ i


-- created on 2026-10-23

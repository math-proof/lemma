import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.RevealmentConstruction
open Finset StatMech.Lattice StatMech StatMech.OSSS StatMech.OSSS.RevealmentConstruction


/--
[mem_queried_buildTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma mem_queried_buildTree_eq
  [Fintype E]
  [DecidableEq E]
  {guard : State → E → Bool}
  {step : State → E → Bool → State}
  {base : State → Bool}
  {ω : ConfigSpace E}
  {l : List E}
  {σ : State}
  {i : E}
-- given
  (Inv : State → Prop)
  (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
  (hσ : Inv σ)
  (hi : i ∈ (buildTree guard step base l σ).queried ω) :
-- imply
  ∃ τ, Inv τ ∧ guard τ i = true := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.mem_queried_buildTree guard step base Inv ω hstep l σ hσ i hi

/--
[eval_buildTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma eval_buildTree_eq
  [Fintype E]
  [DecidableEq E]
  {guard : State → E → Bool}
  {step : State → E → Bool → State}
  {base : State → Bool}
  {ω : ConfigSpace E}
  {l : List E}
  {σ : State} :
-- imply
  (buildTree guard step base l σ).eval ω = base (runState guard step ω l σ) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.eval_buildTree guard step base ω l σ

/--
[runState_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma runState_inv_eq
  [Fintype E]
  [DecidableEq E]
  {guard : State → E → Bool}
  {step : State → E → Bool → State}
  {ω : ConfigSpace E}
  {l : List E}
  {σ : State}
-- given
  (Inv : State → Prop)
  (hstep : ∀ σ e, Inv σ → guard σ e = true → Inv (step σ e (ω e)))
  (hσ : Inv σ) :
-- imply
  Inv (runState guard step ω l σ) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.runState_inv guard step Inv ω hstep l σ hσ

/--
[ReachOpen.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma trans_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {x y z : V}
-- given
  (hxy : ReachOpen endU endV ω x y)
  (hyz : ReachOpen endU endV ω y z) :
-- imply
  ReachOpen endU endV ω x z := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.ReachOpen.trans hxy hyz

/--
[connOpenSet_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma connOpenSet_of_mem_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {x : V}
  {B : Set V}
-- given
  (hx : x ∈ B) :
-- imply
  ConnOpenSet endU endV ω x B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.connOpenSet_of_mem hx

/--
[connOpenSet_prop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma connOpenSet_prop_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {B : Set V}
  {e : E}
-- given
  (hopen : ω e = true)
  (hU : ConnOpenSet endU endV ω (endU e) B) :
-- imply
  ConnOpenSet endU endV ω (endV e) B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.connOpenSet_prop hopen hU

/--
[connOpenSet_prop'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma connOpenSet_prop'_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {B : Set V}
  {e : E}
-- given
  (hopen : ω e = true)
  (hV : ConnOpenSet endU endV ω (endV e) B) :
-- imply
  ConnOpenSet endU endV ω (endU e) B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.connOpenSet_prop' hopen hV

/--
[geomInv_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma geomInv_step_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {B : Set V}
  {disc : Finset V}
  {e : E}
-- given
  (hInv : geomInv endU endV ω B disc)
  (hg : geomGuard endU endV disc e = true) :
-- imply
  geomInv endU endV ω B (geomStep endU endV disc e (ω e)) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.geomInv_step endU endV ω B disc e hInv hg

/--
[queried_exploreTree_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma queried_exploreTree_imp_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {base : Finset V → Bool}
  {ω : ConfigSpace E}
  {B : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {i : E}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (hi : i ∈ (exploreTree endU endV base l disc₀).queried ω) :
-- imply
  ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.queried_exploreTree_imp endU endV base ω B l disc₀ hdisc₀ i hi

/--
[reveal_exploreTree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma reveal_exploreTree_le_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {ν : E → Bool → ℝ}
  {endU endV : E → V}
  {base : Finset V → Bool}
  {B : Set V}
  {l : List E}
  {disc₀ : Finset V}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  reveal ν (exploreTree endU endV base l disc₀) i ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0) + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.reveal_exploreTree_le hν endU endV base B l disc₀ hdisc₀ i

/--
[liftCfg_apply_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma liftCfg_apply_edge_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {ω : ConfigSpace E}
  {e : E}
-- given
  (hinj : Function.Injective edge) :
-- imply
  liftCfg edge ω (edge e) = ω e := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.liftCfg_apply_edge hinj ω e

/--
[reachOpen_imp_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma reachOpen_imp_connected_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {ω : ConfigSpace E}
  {x y : Site d}
-- given
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (h : ReachOpen endU endV ω x y) :
-- imply
  Connected d (liftCfg edge ω) x y := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.reachOpen_imp_connected hinj hcoh hadj h

/--
[connOpenSet_imp_connectedToSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma connOpenSet_imp_connectedToSet_eq
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
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (h : ConnOpenSet endU endV ω x B) :
-- imply
  ConnectedToSet d (liftCfg edge ω) x B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.connOpenSet_imp_connectedToSet hinj hcoh hadj h

/--
[expect_indicator_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma expect_indicator_mono_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (hν : IsProbWeight ν)
  (P Q : ConfigSpace E → Prop)
  (h : ∀ ω, P ω → Q ω) :
-- imply
  expect ν (fun ω => if P ω then (1 : ℝ) else 0) ≤ expect ν (fun ω => if Q ω then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.expect_indicator_mono hν P Q h

/--
[reveal_exploreTree_le_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma reveal_exploreTree_le_connected_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {d : ℕ}
  {ν : E → Bool → ℝ}
  {edge : E → Sym2 (Site d)}
  {endU endV : E → Site d}
  {base : Finset (Site d) → Bool}
  {B : Set (Site d)}
  {l : List E}
  {disc₀ : Finset (Site d)}
  {i : E}
-- given
  (hν : IsProbWeight ν)
  (hinj : Function.Injective edge)
  (hcoh : ∀ e, edge e = s(endU e, endV e))
  (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  reveal ν (exploreTree endU endV base l disc₀) i ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) B then (1 : ℝ) else 0) + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) B then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.reveal_exploreTree_le_connected hν hinj hcoh hadj base B l disc₀ hdisc₀ i

/--
[runState_geomInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma runState_geomInv_eq
  [Fintype E]
  [DecidableEq E]
  [DecidableEq V]
  {endU endV : E → V}
  {ω : ConfigSpace E}
  {B : Set V}
  {l : List E}
  {disc₀ : Finset V}
-- given
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) :
-- imply
  geomInv endU endV ω B (runState (geomGuard endU endV) (geomStep endU endV) ω l disc₀) := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.runState_geomInv endU endV ω B l disc₀ hdisc₀

/--
[eval_exploreTree_imp_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentConstruction.lean)
-/
@[path]
private lemma eval_exploreTree_imp_conn_eq
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
  (hdisc₀ : ∀ x ∈ disc₀, x ∈ B)
  (h : (exploreTree endU endV (fun disc => decide (o ∈ disc)) l disc₀).eval ω = true) :
-- imply
  ConnOpenSet endU endV ω o B := by
-- proof
  apply StatMech.OSSS.RevealmentConstruction.eval_exploreTree_imp_conn endU endV o B l disc₀ hdisc₀ ω h


-- created on 2026-10-23

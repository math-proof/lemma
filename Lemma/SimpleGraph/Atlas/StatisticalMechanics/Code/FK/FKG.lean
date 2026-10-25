import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.FKG
open SimpleGraph Finset StatMech StatMech.FK


/--
[reachable_sup_edge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma reachable_sup_edge_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y a b : V} :
-- imply
  (G ⊔ edge x y).Reachable a b ↔ G.Reachable a b ∨ (G.Reachable a x ∧ G.Reachable y b) ∨ (G.Reachable a y ∧ G.Reachable x b) := by
-- proof
  apply StatMech.FK.reachable_sup_edge_iff x y a b

/--
[card_connectedComponent_le_sup_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_le_sup_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V} :
-- imply
  Nat.card G.ConnectedComponent ≤ Nat.card (G ⊔ edge x y).ConnectedComponent + 1 := by
-- proof
  apply StatMech.FK.card_connectedComponent_le_sup_edge G x y

/--
[card_connectedComponent_sup_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_sup_edge_le_eq
  [Fintype V]
  [DecidableEq V]
  [Finite V]
  {G : SimpleGraph V}
  {x y : V} :
-- imply
  Nat.card (G ⊔ edge x y).ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_sup_edge_le G x y

/--
[card_connectedComponent_sup_edge_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_sup_edge_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (hxy : G.Reachable x y) :
-- imply
  Nat.card (G ⊔ edge x y).ConnectedComponent = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_sup_edge_of_reachable hxy

/--
[card_connectedComponent_sup_edge_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_sup_edge_lt_eq
  [Fintype V]
  [DecidableEq V]
  [Finite V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (hxy : ¬ G.Reachable x y) :
-- imply
  Nat.card (G ⊔ edge x y).ConnectedComponent < Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_sup_edge_lt hxy

/--
[card_connectedComponent_marginal_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_marginal_edge_eq
  [Fintype V]
  [DecidableEq V]
  [Finite V]
  {A B : SimpleGraph V}
  {x y : V}
-- given
  (hAB : A ≤ B) :
-- imply
  Nat.card (A ⊔ edge x y).ConnectedComponent + Nat.card B.ConnectedComponent ≤ Nat.card A.ConnectedComponent + Nat.card (B ⊔ edge x y).ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_marginal_edge hAB x y

/--
[card_connectedComponent_marginal_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_marginal_finset_eq
  [Fintype V]
  [DecidableEq V]
  [Finite V]
  {S : Finset (Sym2 V)} :
-- imply
  ∀ (A B : SimpleGraph V), A ≤ B → Nat.card (A ⊔ fromEdgeSet (↑S)).ConnectedComponent + Nat.card B.ConnectedComponent ≤ Nat.card A.ConnectedComponent + Nat.card (B ⊔ fromEdgeSet (↑S)).ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_marginal_finset S

/--
[card_connectedComponent_marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_marginal_eq
  [Fintype V]
  [DecidableEq V]
  {A B : SimpleGraph V}
  {K : SimpleGraph V}
  [DecidableRel K.Adj]
-- given
  (hAB : A ≤ B) :
-- imply
  Nat.card (A ⊔ K).ConnectedComponent + Nat.card B.ConnectedComponent ≤ Nat.card A.ConnectedComponent + Nat.card (B ⊔ K).ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_marginal hAB K

/--
[card_connectedComponent_submodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma card_connectedComponent_submodular_eq
  [Fintype V]
  [DecidableEq V]
  {G₁ G₂ : SimpleGraph V}
  [DecidableRel G₁.Adj]
  [DecidableRel G₂.Adj] :
-- imply
  Nat.card G₁.ConnectedComponent + Nat.card G₂.ConnectedComponent ≤ Nat.card (G₁ ⊔ G₂).ConnectedComponent + Nat.card (G₁ ⊓ G₂).ConnectedComponent := by
-- proof
  apply StatMech.FK.card_connectedComponent_submodular G₁ G₂

/--
[openSub_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma openSub_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  openSub G (a ⊔ b) = openSub G a ⊔ openSub G b := by
-- proof
  apply StatMech.FK.openSub_sup G a b

/--
[openSub_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma openSub_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  openSub G (a ⊓ b) = openSub G a ⊓ openSub G b := by
-- proof
  apply StatMech.FK.openSub_inf G a b

/--
[numClusters_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma numClusters_supermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  numClusters G a + numClusters G b ≤ numClusters G (a ⊔ b) + numClusters G (a ⊓ b) := by
-- proof
  apply StatMech.FK.numClusters_supermodular G a b

/--
[edgeProduct_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma edgeProduct_logModular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {a b : ConfigSpace (Sym2 V)} :
-- imply
  edgeProduct G p a * edgeProduct G p b = edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b) := by
-- proof
  apply StatMech.FK.edgeProduct_logModular G p a b

/--
[fkWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma fkWeight_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  fkWeight G p q a * fkWeight G p q b ≤ fkWeight G p q (a ⊔ b) * fkWeight G p q (a ⊓ b) := by
-- proof
  apply StatMech.FK.fkWeight_logSupermodular G hp hp1 hq a b

/--
[fkProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma fkProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (fun ω => fkProb G p q ω) := by
-- proof
  apply StatMech.FK.fkProb_FKGLatticeCondition G hp hp1 hq

/--
[fkProb_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma fkProb_positively_associated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {f g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ ω, fkProb G p q ω * f ω) * (∑ ω, fkProb G p q ω * g ω) ≤ ∑ ω, fkProb G p q ω * (f ω * g ω) := by
-- proof
  apply StatMech.FK.fkProb_positively_associated G hp hp1 hq hf hg

/--
[fkProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKG.lean)
-/
@[path]
private lemma fkProb_positively_associated_events_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {A B : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (∑ ω, fkProb G p q ω * A.indicator (fun _ => (1 : ℝ)) ω) * (∑ ω, fkProb G p q ω * B.indicator (fun _ => (1 : ℝ)) ω) ≤ ∑ ω, fkProb G p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.FK.fkProb_positively_associated_events G hp hp1 hq hA hB


-- created on 2026-10-23

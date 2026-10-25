import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
open SimpleGraph StatMech StatMech.FK


/--
[indicator_diff_le_edgeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma indicator_diff_le_edgeSum_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {ω ω' : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (h : ω ≤ ω') :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ω' - A.indicator (fun _ => (1 : ℝ)) ω ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) := by
-- proof
  apply StatMech.FK.indicator_diff_le_edgeSum hA h

/--
[eventMass_eq_coupling_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma eventMass_eq_coupling_snd_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν) :
-- imply
  eventMassProb ν A = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.2 * P z := by
-- proof
  apply StatMech.FK.eventMass_eq_coupling_snd hP A

/--
[eventMass_eq_coupling_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma eventMass_eq_coupling_fst_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν) :
-- imply
  eventMassProb μ A = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.1 * P z := by
-- proof
  apply StatMech.FK.eventMass_eq_coupling_fst hP A

/--
[edgeMarg_eq_coupling_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma edgeMarg_eq_coupling_snd_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hP : IsMonotoneCouplingFun P μ ν) :
-- imply
  edgeMargProb ν e = ∑ z : ConfigSpace E × ConfigSpace E, (if z.2 e then (1 : ℝ) else 0) * P z := by
-- proof
  apply StatMech.FK.edgeMarg_eq_coupling_snd hP e

/--
[edgeMarg_eq_coupling_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma edgeMarg_eq_coupling_fst_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hP : IsMonotoneCouplingFun P μ ν) :
-- imply
  edgeMargProb μ e = ∑ z : ConfigSpace E × ConfigSpace E, (if z.1 e then (1 : ℝ) else 0) * P z := by
-- proof
  apply StatMech.FK.edgeMarg_eq_coupling_fst hP e

/--
[eventMass_diff_le_edgeMarg_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma eventMass_diff_le_edgeMarg_sum_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν)
  (hA : IsIncreasing A) :
-- imply
  eventMassProb ν A - eventMassProb μ A ≤ ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) := by
-- proof
  apply StatMech.FK.eventMass_diff_le_edgeMarg_sum hP hA

/--
[coupling_eventMass_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma coupling_eventMass_le_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν)
  (hA : IsIncreasing A) :
-- imply
  eventMassProb μ A ≤ eventMassProb ν A := by
-- proof
  apply StatMech.FK.coupling_eventMass_le hP hA

/--
[eventMass_eq_of_edgeMarg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma eventMass_eq_of_edgeMarg_eq_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν)
  (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
  (hA : IsIncreasing A) :
-- imply
  eventMassProb μ A = eventMassProb ν A := by
-- proof
  apply StatMech.FK.eventMass_eq_of_edgeMarg_eq hP hmarg hA

/--
[edgeMargProb_fkProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma edgeMargProb_fkProb_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V} :
-- imply
  edgeMargProb (fkProb G p q) e = edgeMarginalOpen G p q e := by
-- proof
  apply StatMech.FK.edgeMargProb_fkProb G p q e

/--
[numClustersBC_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma numClustersBC_antitone_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C ≤ C') :
-- imply
  numClustersBC G C' ω ≤ numClustersBC G C ω := by
-- proof
  apply StatMech.FK.numClustersBC_antitone G C C' hCC' ω

/--
[bcWeight_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma bcWeight_antitone_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  bcWeight G C' p q ω ≤ bcWeight G C p q ω := by
-- proof
  apply StatMech.FK.bcWeight_antitone G C C' hCC' hp hp1 hq ω

/--
[bcWeight_qpow_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma bcWeight_qpow_le_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {N : ℕ}
  {ω : ConfigSpace (Sym2 V)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hb : numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
-- imply
  bcWeight G C p q ω ≤ q ^ N * bcWeight G C' p q ω := by
-- proof
  apply StatMech.FK.bcWeight_qpow_le G C C' hp hp1 hq N ω hb

/--
[bcZ_qpow_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma bcZ_qpow_le_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N) :
-- imply
  bcZ G C p q ≤ q ^ N * bcZ G C' p q := by
-- proof
  apply StatMech.FK.bcZ_qpow_le G C C' hp hp1 hq N hb

/--
[bcEventMass_le_qpow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma bcEventMass_le_qpow_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C C' : SimpleGraph V}
  [DecidableRel C.Adj]
  [DecidableRel C'.Adj]
  {p q : ℝ}
  {N : ℕ}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hCC' : C ≤ C')
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hb : ∀ ω, numClustersBC G C ω ≤ numClustersBC G C' ω + N)
  (hA0 : ∀ ω, 0 ≤ A.indicator (fun _ => (1 : ℝ)) ω) :
-- imply
  bcEventMass G C' p q A ≤ q ^ N * bcEventMass G C p q A := by
-- proof
  apply StatMech.FK.bcEventMass_le_qpow G C C' hCC' hp hp1 hq N hb hA0

/--
[card_connectedComponent_le_sup_fromEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma card_connectedComponent_le_sup_fromEdgeSet_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset (Sym2 V)} :
-- imply
  ∀ A : SimpleGraph V, Nat.card A.ConnectedComponent ≤ Nat.card (A ⊔ fromEdgeSet (↑S)).ConnectedComponent + S.card := by
-- proof
  apply StatMech.FK.card_connectedComponent_le_sup_fromEdgeSet G S

/--
[numClustersBC_bot_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean)
-/
@[path]
private lemma numClustersBC_bot_le_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  numClustersBC G (⊥ : SimpleGraph V) ω ≤ numClustersBC G C' ω + C'.edgeFinset.card := by
-- proof
  apply StatMech.FK.numClustersBC_bot_le G C' ω


-- created on 2026-10-23

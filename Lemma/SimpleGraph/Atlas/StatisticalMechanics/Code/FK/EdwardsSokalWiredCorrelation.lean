import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part3
open StatMech StatMech.IsingFK


/--
[sum_pottsBoundaryObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma sum_pottsBoundaryObservable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
-- given
  (bdry : V → Prop) :
-- imply
  ∑ a : Fin q, pottsBoundaryObservable q b a = 0 := by
-- proof
  apply StatMech.IsingFK.sum_pottsBoundaryObservable G bdry q b

/--
[sum_pinned_eq_filterQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma sum_pinned_eq_filterQ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {q : Nat}
  {c0 : C}
  {b : Fin q}
  {F : (C → Fin q) → Real}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ tau : {tau : C → Fin q // tau c0 = b}, F tau.1) = ∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b), F tau := by
-- proof
  apply StatMech.IsingFK.sum_pinned_eq_filterQ G bdry c0 b F

/--
[colour_pottsBoundary_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma colour_pottsBoundary_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {c0 cx : C}
-- given
  (bdry : V → Prop)
  (h : cx ≠ c0) :
-- imply
  (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b), pottsBoundaryObservable q b (tau cx)) = 0 := by
-- proof
  apply StatMech.IsingFK.colour_pottsBoundary_cancel G bdry q b c0 cx h

/--
[colour_pottsBoundary_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma colour_pottsBoundary_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  [Fintype C]
  [DecidableEq C]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {c0 cx : C}
-- given
  (bdry : V → Prop)
  (h : cx = c0) :
-- imply
  (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b), pottsBoundaryObservable q b (tau cx)) = ((q : Real) - 1) * (q : Real) ^ (Fintype.card C - 1) := by
-- proof
  apply StatMech.IsingFK.colour_pottsBoundary_const G bdry q b c0 cx h

/--
[colour_pottsBoundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma colour_pottsBoundary_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {omega : ConfigSpace (Sym2 V)}
  {v0 : V}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv0 : bdry v0) :
-- imply
  (∑ sigma ∈ Finset.univ.filter (fun sigma : V → Fin q => ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma), pottsBoundaryObservable q b (sigma x)) = if ConnToBdry G bdry omega x then ((q : Real) - 1) * (q : Real) ^ (Fintype.card (wiredSub G bdry omega).ConnectedComponent - 1) else 0 := by
-- proof
  apply StatMech.IsingFK.colour_pottsBoundary_sum G bdry b omega v0 hv0 x

/--
[esWeightWired_pottsBoundary_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma esWeightWired_pottsBoundary_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {p : Real}
  {omega : ConfigSpace (Sym2 V)}
  {v0 : V}
  {x : V}
-- given
  (bdry : V → Prop)
  (hv0 : bdry v0) :
-- imply
  (∑ sigma : V → Fin q, esWeightWired G bdry b p sigma omega * pottsBoundaryObservable q b (sigma x)) = edgeProduct G p omega * (if ConnToBdry G bdry omega x then ((q : Real) - 1) * (q : Real) ^ (numClustersBC G (boundaryCliqueGraph bdry) omega - 1) else 0) := by
-- proof
  apply StatMech.IsingFK.esWeightWired_pottsBoundary_sum G bdry b p omega v0 hv0 x

/--
[esWiredPottsCenteredOnePoint_eq_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma esWiredPottsCenteredOnePoint_eq_conn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {p : Real}
  {x v0 : V}
-- given
  (bdry : V → Prop)
  (hv0 : bdry v0) :
-- imply
  esWiredPottsCenteredOnePoint G bdry q b p x = ((q : Real) - 1) * wiredConnToBdryProbQ G bdry q p x := by
-- proof
  apply StatMech.IsingFK.esWiredPottsCenteredOnePoint_eq_conn G bdry q b p x v0 hv0

/--
[esWiredPottsCenteredOnePoint_eq_potts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma esWiredPottsCenteredOnePoint_eq_potts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  esWiredPottsCenteredOnePoint G bdry q b (1 - Real.exp (-(beta * J))) x = ∑ sigma : V → Fin q, pottsProbWired G bdry q b beta J sigma * pottsBoundaryObservable q b (sigma x) := by
-- proof
  apply StatMech.IsingFK.esWiredPottsCenteredOnePoint_eq_potts G bdry q b beta J x

/--
[pottsBoundaryObservable_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma pottsBoundaryObservable_expectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  (∑ sigma : V → Fin q, pottsProbWired G bdry q b beta J sigma * pottsBoundaryObservable q b (sigma x)) = (q : Real) * pottsBoundaryProbWired G bdry q b beta J x - 1 := by
-- proof
  apply StatMech.IsingFK.pottsBoundaryObservable_expectation G bdry q b beta J x

/--
[pottsBoundaryProbWired_sub_inv_eq_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma pottsBoundaryProbWired_sub_inv_eq_conn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  [NeZero q]
  {b : Fin q}
  {beta J : Real}
  {x v0 : V}
-- given
  (bdry : V → Prop)
  (hv0 : bdry v0) :
-- imply
  pottsBoundaryProbWired G bdry q b beta J x - 1 / (q : Real) = ((q : Real) - 1) / q * wiredConnToBdryProbQ G bdry q (1 - Real.exp (-(beta * J))) x := by
-- proof
  apply StatMech.IsingFK.pottsBoundaryProbWired_sub_inv_eq_conn G bdry q b beta J x v0 hv0

/--
[wiredConnToBdryProbQ_eq_wiredFkProb_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean)
-/
@[path]
private lemma wiredConnToBdryProbQ_eq_wiredFkProb_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {q : Nat}
  {p : Real}
  {x : V}
-- given
  (bdry : V → Prop) :
-- imply
  wiredConnToBdryProbQ G bdry q p x = ∑ omega ∈ Finset.univ.filter (fun omega : ConfigSpace (Sym2 V) => ConnToBdry G bdry omega x), wiredFkProb G bdry p (q : Real) omega := by
-- proof
  apply StatMech.IsingFK.wiredConnToBdryProbQ_eq_wiredFkProb_sum G bdry q p x


-- created on 2026-10-23

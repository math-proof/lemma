import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEdges
open Finset StatMech StatMech.FK


/--
[activeBCWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeBCWeight G C pf q omega := by
-- proof
  apply StatMech.FK.activeBCWeight_pos G C hpf hpf1 hq omega

/--
[activeBCZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeBCZ G C pf q := by
-- proof
  apply StatMech.FK.activeBCZ_pos G C hpf hpf1 hq

/--
[activeBCProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeBCProb G C pf q omega := by
-- proof
  apply StatMech.FK.activeBCProb_pos G C hpf hpf1 hq omega

/--
[activeBCProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  ∑ omega, activeBCProb G C pf q omega = 1 := by
-- proof
  apply StatMech.FK.activeBCProb_sum_eq_one G C hpf hpf1 hq

/--
[activeBCWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCWeight_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega eta : ConfigSpace G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  activeBCWeight G C pf q omega * activeBCWeight G C pf q eta <= activeBCWeight G C pf q (omega ⊔ eta) * activeBCWeight G C pf q (omega ⊓ eta) := by
-- proof
  apply StatMech.FK.activeBCWeight_logSupermodular G C hpf hpf1 hq omega eta

/--
[activeBCProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  FKGLatticeCondition (activeBCProb G C pf q) := by
-- proof
  apply StatMech.FK.activeBCProb_FKGLatticeCondition G C hpf hpf1 hq

/--
[activeBCWeight_close_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCWeight_close_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {e : G.edgeSet}
  {omega : ConfigSpace G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  (1 - pf e.1) * activeBCWeight G C pf q (setOpen e omega) <= pf e.1 * activeBCWeight G C pf q (setClosed e omega) := by
-- proof
  apply StatMech.FK.activeBCWeight_close_pair G C hpf hpf1 hq e omega

/--
[activeBC_openMarginal_le_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBC_openMarginal_le_param_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {e : G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  openMarginal (activeBCProb G C pf q) e <= pf e.1 := by
-- proof
  apply StatMech.FK.activeBC_openMarginal_le_param G C hpf hpf1 hq e

/--
[activeBC_prod_closed_param_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBC_prod_closed_param_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {S : Finset G.edgeSet}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  S.prod (fun e => 1 - pf e.1) <= ∑ omega, activeBCProb G C pf q omega * closedProd S omega := by
-- proof
  apply StatMech.FK.activeBC_prod_closed_param_le G C hpf hpf1 hq S

/--
[hasDerivAt_activeBCWeight_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeBCWeight_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V -> Real}
  {beta : Real}
  {q : Real}
  {omega : ConfigSpace G.edgeSet}
-- given
  (hJ : forall e, 0 < J e)
  (hbeta : 0 < beta) :
-- imply
  HasDerivAt (fun b => activeBCWeight G C (betaParams J b) q omega) (activeBCWeight G C (betaParams J beta) q omega * activeBetaScore G J beta omega) beta := by
-- proof
  apply StatMech.FK.hasDerivAt_activeBCWeight_beta G C hJ hbeta q omega

/--
[hasDerivAt_activeBCNumer_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeBCNumer_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V -> Real}
  {beta : Real}
  {q : Real}
-- given
  (hJ : forall e, 0 < J e)
  (hbeta : 0 < beta)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  HasDerivAt (fun b => activeBCNumer G C (betaParams J b) q f) (activeBCNumer G C (betaParams J beta) q (fun omega => f omega * activeBetaScore G J beta omega)) beta := by
-- proof
  apply StatMech.FK.hasDerivAt_activeBCNumer_beta G C hJ hbeta q f

/--
[activeBCNumer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCNumer_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
-- given
  (pf : Sym2 V -> Real) :
-- imply
  activeBCNumer G C pf q (fun _ => 1) = activeBCZ G C pf q := by
-- proof
  apply StatMech.FK.activeBCNumer_one G C pf q

/--
[activeBCMean_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCMean_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
-- given
  (pf : Sym2 V -> Real)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C pf q f = activeBCNumer G C pf q f / activeBCZ G C pf q := by
-- proof
  apply StatMech.FK.activeBCMean_eq_div G C pf q f

/--
[activeBCMean_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCMean_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
-- given
  (pf : Sym2 V -> Real)
  (f g : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C pf q (fun omega => f omega + g omega) = activeBCMean G C pf q f + activeBCMean G C pf q g := by
-- proof
  apply StatMech.FK.activeBCMean_add G C pf q f g

/--
[activeBCMean_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCMean_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q c : Real}
-- given
  (pf : Sym2 V -> Real)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C pf q (fun omega => c * f omega) = c * activeBCMean G C pf q f := by
-- proof
  apply StatMech.FK.activeBCMean_const_mul G C pf q c f

/--
[activeBCMean_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCMean_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
  [Fintype I]
-- given
  (pf : Sym2 V -> Real)
  (g : I -> ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C pf q (fun omega => ∑ i, g i omega) = ∑ i, activeBCMean G C pf q (g i) := by
-- proof
  apply StatMech.FK.activeBCMean_sum G C pf q g

/--
[activeBCCov_const_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCCov_const_mul_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q c : Real}
-- given
  (pf : Sym2 V -> Real)
  (f g : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCCov G C pf q f (fun omega => c * g omega) = c * activeBCCov G C pf q f g := by
-- proof
  apply StatMech.FK.activeBCCov_const_mul_right G C pf q c f g

/--
[activeBCCov_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCCov_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
  [Fintype I]
-- given
  (pf : Sym2 V -> Real)
  (f : ConfigSpace G.edgeSet -> Real)
  (g : I -> ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCCov G C pf q f (fun omega => ∑ i, g i omega) = ∑ i, activeBCCov G C pf q f (g i) := by
-- proof
  apply StatMech.FK.activeBCCov_sum_right G C pf q f g

/--
[activeBCCov_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma activeBCCov_sub_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {c : Real}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q)
  (f g : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCCov G C pf q f (fun omega => g omega - c) = activeBCCov G C pf q f g := by
-- proof
  apply StatMech.FK.activeBCCov_sub_const G C hpf hpf1 hq f g c

/--
[hasDerivAt_activeBCMean_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeBCMean_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V -> Real}
  {beta : Real}
  {q : Real}
-- given
  (hJ : forall e, 0 < J e)
  (hbeta : 0 < beta)
  (hq : 0 < q)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  HasDerivAt (fun b => activeBCMean G C (betaParams J b) q f) (∑ e : G.edgeSet, (J e.1 / betaParams J beta e.1) * activeBCCov G C (betaParams J beta) q f (OSSS.Lindeberg.coord e)) beta := by
-- proof
  apply StatMech.FK.hasDerivAt_activeBCMean_beta_sum G C hJ hbeta hq f

/--
[hasDerivAt_activeBCProbOf_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeBCProbOf_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {J : Sym2 V -> Real}
  {beta : Real}
  {q : Real}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hJ : forall e, 0 < J e)
  (hbeta : 0 < beta)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun b => activeBCProbOf G C (betaParams J b) q A) (∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) * activeBCCov G C (betaParams J beta) q (A.indicator fun _ => (1 : Real)) (OSSS.Lindeberg.coord e)) beta := by
-- proof
  apply StatMech.FK.hasDerivAt_activeBCProbOf_beta_sum G C hJ hbeta hq A


-- created on 2026-10-23

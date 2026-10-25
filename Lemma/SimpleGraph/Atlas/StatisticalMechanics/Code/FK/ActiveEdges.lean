import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
open Finset StatMech StatMech.FK


/--
[extendActive_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma extendActive_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace G.edgeSet}
  {e : G.edgeSet} :
-- imply
  extendActive G ω e.1 = ω e := by
-- proof
  apply StatMech.FK.extendActive_apply G ω e

/--
[extendActive_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma extendActive_sup_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω η : ConfigSpace G.edgeSet} :
-- imply
  extendActive G (ω ⊔ η) = extendActive G ω ⊔ extendActive G η := by
-- proof
  apply StatMech.FK.extendActive_sup G ω η

/--
[extendActive_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma extendActive_inf_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω η : ConfigSpace G.edgeSet} :
-- imply
  extendActive G (ω ⊓ η) = extendActive G ω ⊓ extendActive G η := by
-- proof
  apply StatMech.FK.extendActive_inf G ω η

/--
[extendActive_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma extendActive_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeSet}
  {ω : ConfigSpace G.edgeSet} :
-- imply
  extendActive G (setOpen e ω) = setOpen e.1 (extendActive G ω) := by
-- proof
  apply StatMech.FK.extendActive_setOpen G e ω

/--
[extendActive_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma extendActive_setClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {e : G.edgeSet}
  {ω : ConfigSpace G.edgeSet} :
-- imply
  extendActive G (setClosed e ω) = setClosed e.1 (extendActive G ω) := by
-- proof
  apply StatMech.FK.extendActive_setClosed G e ω

/--
[activeWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeWeight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeWeight G pf q ω := by
-- proof
  apply StatMech.FK.activeWeight_pos G hpf hpf1 hq ω

/--
[activeZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeZ_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeZ G pf q := by
-- proof
  apply StatMech.FK.activeZ_pos G hpf hpf1 hq

/--
[activeProb_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeProb_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < activeProb G pf q ω := by
-- proof
  apply StatMech.FK.activeProb_pos G hpf hpf1 hq ω

/--
[activeProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeProb_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  ∑ ω, activeProb G pf q ω = 1 := by
-- proof
  apply StatMech.FK.activeProb_sum_eq_one G hpf hpf1 hq

/--
[activeWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeWeight_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {ω η : ConfigSpace G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  activeWeight G pf q ω * activeWeight G pf q η ≤ activeWeight G pf q (ω ⊔ η) * activeWeight G pf q (ω ⊓ η) := by
-- proof
  apply StatMech.FK.activeWeight_logSupermodular G hpf hpf1 hq ω η

/--
[activeProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeProb_FKGLatticeCondition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  FKGLatticeCondition (activeProb G pf q) := by
-- proof
  apply StatMech.FK.activeProb_FKGLatticeCondition G hpf hpf1 hq

/--
[edgeProductW_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma edgeProductW_setOpen_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e : G.edgeSet}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProductW G pf (setOpen e.1 ω) = (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) * pf e.1 := by
-- proof
  apply StatMech.FK.edgeProductW_setOpen G pf e ω

/--
[edgeProductW_setClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma edgeProductW_setClosed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {e : G.edgeSet}
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  edgeProductW G pf (setClosed e.1 ω) = (∏ a ∈ G.edgeFinset.erase e.1, (if ω a then pf a else 1 - pf a)) * (1 - pf e.1) := by
-- proof
  apply StatMech.FK.edgeProductW_setClosed G pf e ω

/--
[activeWeight_close_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeWeight_close_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e : G.edgeSet}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  (1 - pf e.1) * activeWeight G pf q (setOpen e ω) ≤ pf e.1 * activeWeight G pf q (setClosed e ω) := by
-- proof
  apply StatMech.FK.activeWeight_close_pair G hpf hpf1 hq e ω

/--
[openMarginal_eq_closedFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma openMarginal_eq_closedFiber_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {e : E} :
-- imply
  openMarginal μ e = ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false), μ (setOpen e ψ) := by
-- proof
  apply StatMech.FK.openMarginal_eq_closedFiber G μ e

/--
[activeClosedFiber_pairMass_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeClosedFiber_pairMass_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ ψ ∈ Finset.univ.filter (fun ψ : ConfigSpace E => ψ e = false), (μ (setOpen e ψ) + μ (setClosed e ψ)) = 1 := by
-- proof
  apply StatMech.FK.activeClosedFiber_pairMass_eq_one G μ hμ1 e

/--
[openMarginal_le_of_close_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma openMarginal_le_of_close_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {e : E}
  {p : ℝ}
-- given
  (hμ1 : ∑ ω, μ ω = 1)
  (hpair : ∀ ψ, (1 - p) * μ (setOpen e ψ) ≤ p * μ (setClosed e ψ)) :
-- imply
  openMarginal μ e ≤ p := by
-- proof
  apply StatMech.FK.openMarginal_le_of_close_pair G μ hμ1 e hpair

/--
[active_openMarginal_le_param](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma active_openMarginal_le_param_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {e : G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  openMarginal (activeProb G pf q) e ≤ pf e.1 := by
-- proof
  apply StatMech.FK.active_openMarginal_le_param G hpf hpf1 hq e

/--
[closedProd_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma closedProd_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {S : Finset E} :
-- imply
  Antitone (closedProd S) := by
-- proof
  apply StatMech.FK.closedProd_antitone G S

/--
[closedProd_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma closedProd_insert_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {e : E}
  {S : Finset E}
  {ω : ConfigSpace E}
-- given
  (he : e ∉ S) :
-- imply
  closedProd (insert e S) ω = closedProd S ω * closedProd {e} ω := by
-- proof
  apply StatMech.FK.closedProd_insert G he ω

/--
[fkg_inequality_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma fkg_inequality_antitone_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f g : ConfigSpace E → ℝ}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ)
  (hf : Antitone f)
  (hg : Antitone g) :
-- imply
  (∑ ω, μ ω * f ω) * (∑ ω, μ ω * g ω) ≤ ∑ ω, μ ω * (f ω * g ω) := by
-- proof
  apply StatMech.FK.fkg_inequality_antitone G hμ0 hμ1 hFKG hf hg

/--
[mean_closedProd_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma mean_closedProd_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  (∑ ω, μ ω * closedProd {e} ω) = 1 - openMarginal μ e := by
-- proof
  apply StatMech.FK.mean_closedProd_singleton G μ hμ1 e

/--
[prod_one_sub_openMarginal_le_closedProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma prod_one_sub_openMarginal_le_closedProd_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : Finset E}
-- given
  (hμ0 : 0 ≤ μ)
  (hμ1 : ∑ ω, μ ω = 1)
  (hFKG : FKGLatticeCondition μ) :
-- imply
  (∏ e ∈ S, (1 - openMarginal μ e)) ≤ ∑ ω, μ ω * closedProd S ω := by
-- proof
  apply StatMech.FK.prod_one_sub_openMarginal_le_closedProd G μ hμ0 hμ1 hFKG S

/--
[active_prod_closed_param_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma active_prod_closed_param_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {S : Finset G.edgeSet}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 1 ≤ q) :
-- imply
  (∏ e ∈ S, (1 - pf e.1)) ≤ ∑ ω, activeProb G pf q ω * closedProd S ω := by
-- proof
  apply StatMech.FK.active_prod_closed_param_le G hpf hpf1 hq S

/--
[betaScore_extendActive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma betaScore_extendActive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {ω : ConfigSpace G.edgeSet} :
-- imply
  betaScore G J β (extendActive G ω) = activeBetaScore G J β ω := by
-- proof
  apply StatMech.FK.betaScore_extendActive G J β ω

/--
[hasDerivAt_activeWeight_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeWeight_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {ω : ConfigSpace G.edgeSet}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  HasDerivAt (fun b => activeWeight G (betaParams J b) q ω) (activeWeight G (betaParams J β) q ω * activeBetaScore G J β ω) β := by
-- proof
  apply StatMech.FK.hasDerivAt_activeWeight_beta G hJ hβ q ω

/--
[hasDerivAt_activeNumer_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeNumer_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β) :
-- imply
  HasDerivAt (fun b => activeNumer G (betaParams J b) q f) (activeNumer G (betaParams J β) q (fun ω => f ω * activeBetaScore G J β ω)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_activeNumer_beta G hJ hβ q f

/--
[activeNumer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeNumer_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ} :
-- imply
  activeNumer G pf q (fun _ => 1) = activeZ G pf q := by
-- proof
  apply StatMech.FK.activeNumer_one G pf q

/--
[activeMean_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeMean_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeMean G pf q f = activeNumer G pf q f / activeZ G pf q := by
-- proof
  apply StatMech.FK.activeMean_eq_div G pf q f

/--
[activeMean_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeMean_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeMean G pf q (fun ω => f ω + g ω) = activeMean G pf q f + activeMean G pf q g := by
-- proof
  apply StatMech.FK.activeMean_add G pf q f g

/--
[activeMean_const_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeMean_const_mul_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q c : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeMean G pf q (fun ω => c * f ω) = c * activeMean G pf q f := by
-- proof
  apply StatMech.FK.activeMean_const_mul G pf q c f

/--
[activeMean_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeMean_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  [Fintype ι]
  {g : ι → ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeMean G pf q (fun ω => ∑ i, g i ω) = ∑ i, activeMean G pf q (g i) := by
-- proof
  apply StatMech.FK.activeMean_sum G pf q g

/--
[activeCov_const_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeCov_const_mul_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q c : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeCov G pf q f (fun ω => c * g ω) = c * activeCov G pf q f g := by
-- proof
  apply StatMech.FK.activeCov_const_mul_right G pf q c f g

/--
[activeCov_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeCov_sum_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
  [Fintype ι]
  {g : ι → ConfigSpace G.edgeSet → ℝ} :
-- imply
  activeCov G pf q f (fun ω => ∑ i, g i ω) = ∑ i, activeCov G pf q f (g i) := by
-- proof
  apply StatMech.FK.activeCov_sum_right G pf q f g

/--
[activeCov_sub_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma activeCov_sub_const_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {q : ℝ}
  {f g : ConfigSpace G.edgeSet → ℝ}
  {c : ℝ}
-- given
  (hpf : ∀ e, 0 < pf e)
  (hpf1 : ∀ e, pf e < 1)
  (hq : 0 < q) :
-- imply
  activeCov G pf q f (fun ω => g ω - c) = activeCov G pf q f g := by
-- proof
  apply StatMech.FK.activeCov_sub_const G hpf hpf1 hq f g c

/--
[hasDerivAt_activeMean_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeMean_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {f : ConfigSpace G.edgeSet → ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun b => activeMean G (betaParams J b) q f) (∑ e : G.edgeSet, (J e.1 / betaParams J β e.1) * activeCov G (betaParams J β) q f (OSSS.Lindeberg.coord e)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_activeMean_beta_sum G hJ hβ hq f

/--
[hasDerivAt_activeProbOf_beta_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdges.lean)
-/
@[path]
private lemma hasDerivAt_activeProbOf_beta_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → ℝ}
  {β : ℝ}
  {q : ℝ}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hq : 0 < q) :
-- imply
  HasDerivAt (fun b => activeProbOf G (betaParams J b) q A) (∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(β * J e.1)))) * activeCov G (betaParams J β) q (A.indicator (fun _ => (1 : ℝ))) (OSSS.Lindeberg.coord e)) β := by
-- proof
  apply StatMech.FK.hasDerivAt_activeProbOf_beta_sum G hJ hβ hq A


-- created on 2026-10-23

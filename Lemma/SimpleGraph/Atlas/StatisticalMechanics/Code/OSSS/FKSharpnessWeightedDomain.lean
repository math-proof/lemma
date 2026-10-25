import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
open Finset Set StatMech StatMech.FK StatMech.OSSS StatMech.OSSS.FKSharpnessWeightedDomain


/--
[bcWeightW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcWeightW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < bcWeightW G C pf q omega := by
-- proof
  apply StatMech.FK.bcWeightW_pos G C hpf hpf1 hq omega

/--
[bcWeightW_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcWeightW_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 <= bcWeightW G C pf q omega := by
-- proof
  apply StatMech.FK.bcWeightW_nonneg G C hpf hpf1 hq omega

/--
[bcZW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcZW_pos_eq
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
  0 < bcZW G C pf q := by
-- proof
  apply StatMech.FK.bcZW_pos G C hpf hpf1 hq

/--
[bcProbW_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcProbW_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 <= bcProbW G C pf q omega := by
-- proof
  apply StatMech.FK.bcProbW_nonneg G C hpf hpf1 hq omega

/--
[bcProbW_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcProbW_sum_eq_one_eq
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
  ∑ omega, bcProbW G C pf q omega = 1 := by
-- proof
  apply StatMech.FK.bcProbW_sum_eq_one G C hpf hpf1 hq

/--
[bcWeightW_cross_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcWeightW_cross_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  bcWeightW G C pf q a * bcWeightW G C' pf q b <= bcWeightW G C pf q (a ⊓ b) * bcWeightW G C' pf q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcWeightW_cross_bc G C C' hCC' hpf hpf1 hq a b

/--
[bcProbW_cross_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcProbW_cross_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  bcProbW G C pf q a * bcProbW G C' pf q b <= bcProbW G C pf q (a ⊓ b) * bcProbW G C' pf q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcProbW_cross_bc G C C' hCC' hpf hpf1 hq a b

/--
[bcProbW_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcProbW_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C pf q omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C' pf q omega := by
-- proof
  apply StatMech.FK.bcProbW_mono_bc G C C' hCC' hpf hpf1 hq hA

/--
[inducedBcZW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma inducedBcZW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < inducedBcZW G C pf q F psi := by
-- proof
  apply StatMech.FK.inducedBcZW_pos G C hpf hpf1 hq F psi

/--
[condBcProbW_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma condBcProbW_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  (0 : ConfigSpace (Sym2 V) -> Real) <= condBcProbW G C pf q F psi := by
-- proof
  apply StatMech.FK.condBcProbW_nonneg G C hpf hpf1 hq F psi

/--
[condBcProbW_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma condBcProbW_sum_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  ∑ omega, condBcProbW G C pf q F psi omega = 1 := by
-- proof
  apply StatMech.FK.condBcProbW_sum_eq_one G C hpf hpf1 hq F psi

/--
[condBcProbW_cross_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma condBcProbW_cross_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {psi a b : ConfigSpace (Sym2 V)}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q) :
-- imply
  condBcProbW G C pf q F psi a * condBcProbW G C' pf q F psi b <= condBcProbW G C pf q F psi (a ⊓ b) * condBcProbW G C' pf q F psi (a ⊔ b) := by
-- proof
  apply StatMech.FK.condBcProbW_cross_bc G C C' hCC' hpf hpf1 hq F psi a b

/--
[condBcProbW_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma condBcProbW_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {psi : ConfigSpace (Sym2 V)}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * condBcProbW G C pf q F psi omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * condBcProbW G C' pf q F psi omega := by
-- proof
  apply StatMech.FK.condBcProbW_mono_bc G C C' hCC' hpf hpf1 hq F psi hA

/--
[activeBCProb_mono_bc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma activeBCProb_mono_bc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {C' : SimpleGraph V}
  [DecidableRel C'.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {A : Set (ConfigSpace G.edgeSet)}
-- given
  (hCC' : C <= C')
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * activeBCProb G C pf q omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * activeBCProb G C' pf q omega := by
-- proof
  apply StatMech.FK.activeBCProb_mono_bc G C C' hCC' hpf hpf1 hq hA

/--
[bcWeightW_eq_of_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcWeightW_eq_of_edges_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
  {omega eta : ConfigSpace (Sym2 V)}
-- given
  (pf : Sym2 V -> Real)
  (h : forall e, e ∈ G.edgeFinset -> omega e = eta e) :
-- imply
  bcWeightW G C pf q omega = bcWeightW G C pf q eta := by
-- proof
  apply StatMech.FK.bcWeightW_eq_of_edges G C pf q omega eta h

/--
[bcWeightW_activeSplitEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcWeightW_activeSplitEquiv_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  {q : Real}
  {eta : ConfigSpace G.edgeSet}
-- given
  (pf : Sym2 V -> Real)
  (xi : ConfigSpace {e : Sym2 V // e ∉ G.edgeSet}) :
-- imply
  bcWeightW G C pf q ((activeSplitEquiv G).symm (eta, xi)) = activeBCWeight G C pf q eta := by
-- proof
  apply StatMech.FK.bcWeightW_activeSplitEquiv_symm G C pf q eta xi

/--
[activeBCZW_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma activeBCZW_factorization_eq
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
  bcZW G C pf q = 2 ^ ecz_NE G * activeBCZ G C pf q := by
-- proof
  apply StatMech.FK.activeBCZW_factorization G C pf q

/--
[activeBCNumerW_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma activeBCNumerW_factorization_eq
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
  (∑ omega : ConfigSpace (Sym2 V), f (restrictActive G omega) * bcWeightW G C pf q omega) = 2 ^ ecz_NE G * activeBCNumer G C pf q f := by
-- proof
  apply StatMech.FK.activeBCNumerW_factorization G C pf q f

/--
[activeBCMean_eq_bcProbW_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma activeBCMean_eq_bcProbW_lift_eq
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
  (hq : 0 < q)
  (f : ConfigSpace G.edgeSet -> Real) :
-- imply
  activeBCMean G C pf q f = ∑ omega : ConfigSpace (Sym2 V), f (restrictActive G omega) * bcProbW G C pf q omega := by
-- proof
  apply StatMech.FK.activeBCMean_eq_bcProbW_lift G C hpf hpf1 hq f

/--
[ocd_psiEdgeFactorW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_psiEdgeFactorW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfOut : Sym2 Vout -> Real}
  {psi : ConfigSpace (Sym2 Vout)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hpf : forall e, 0 < pfOut e)
  (hpf1 : forall e, pfOut e < 1) :
-- imply
  0 < ocd_psiEdgeFactorW Gout iota pfOut psi := by
-- proof
  apply StatMech.FK.ocd_psiEdgeFactorW_pos G C Gin Gout iota bdryOut hpf hpf1 psi

/--
[ocd_edgeProductW_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_edgeProductW_psiExt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {omega : ConfigSpace (Sym2 Vin)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut) :
-- imply
  edgeProductW Gout pfOut (ocd_psiExt iota psi omega) = edgeProductW Gin pfIn omega * ocd_psiEdgeFactorW Gout iota pfOut psi := by
-- proof
  apply StatMech.FK.ocd_edgeProductW_psiExt G C Gin Gout iota bdryOut hiota hadjm hparam psi omega

/--
[ocd_psiShiftW_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_psiShiftW_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hpf : forall e, 0 < pfOut e)
  (hpf1 : forall e, pfOut e < 1)
  (hq : 0 < q) :
-- imply
  0 < ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
-- proof
  apply StatMech.FK.ocd_psiShiftW_pos G C Gin Gout iota bdryOut hpf hpf1 hq psi

/--
[ocd_bcWeightW_psiExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_bcWeightW_psiExt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {omega : ConfigSpace (Sym2 Vin)}
  {q : Real}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut) :
-- imply
  bcWeightW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_psiExt iota psi omega) = bcWeightW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega * ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
-- proof
  apply StatMech.FK.ocd_bcWeightW_psiExt G C Gin Gout iota bdryOut hiota hadjm hparam psi omega q

/--
[ocd_inducedBcZW_psi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_inducedBcZW_psi_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {q : Real}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut) :
-- imply
  inducedBcZW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi = bcZW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q * ocd_psiShiftW Gout iota bdryOut pfOut psi q := by
-- proof
  apply StatMech.FK.ocd_inducedBcZW_psi G C Gin Gout iota bdryOut hiota hadjm hparam psi q

/--
[ocd_condBcProbW_psiExt_eq_bcProbW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_condBcProbW_psiExt_eq_bcProbW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {omega : ConfigSpace (Sym2 Vin)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 0 < q) :
-- imply
  condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi (ocd_psiExt iota psi omega) = bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega := by
-- proof
  apply StatMech.FK.ocd_condBcProbW_psiExt_eq_bcProbW G C Gin Gout iota bdryOut hiota hadjm hparam hpfOut hpfOut1 hq psi omega

/--
[ocd_condBcProbW_psiExt_sum_eq_inducedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_condBcProbW_psiExt_sum_eq_inducedBox_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho, B.indicator (fun _ => (1 : Real)) rho * condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) = ∑ omega : ConfigSpace (Sym2 Vin), (ocd_psiExt iota psi ⁻¹' B).indicator (fun _ => (1 : Real)) omega * bcProbW Gin (ocd_inducedWiring Gout iota bdryOut psi) pfIn q omega := by
-- proof
  apply StatMech.FK.ocd_condBcProbW_psiExt_sum_eq_inducedBox G C Gin Gout iota bdryOut hiota hadjm hparam hpfOut hpfOut1 hq psi B

/--
[ocd_condBcProbW_psiExt_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_condBcProbW_psiExt_dominated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (bdryIn : Vin -> Prop)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hwire : ocd_inducedWiring Gout iota bdryOut psi <= Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
-- proof
  apply StatMech.FK.ocd_condBcProbW_psiExt_dominated G C Gin Gout iota bdryOut hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq psi hwire hA

/--
[ocd_free_le_condBcProbW_innerRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_free_le_condBcProbW_innerRestrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {psi : ConfigSpace (Sym2 Vout)}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW Gin ⊥ pfIn q omega) <= ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho := by
-- proof
  apply StatMech.FK.ocd_free_le_condBcProbW_innerRestrict G C Gin Gout iota bdryOut hiota hadjm hparam hpfIn hpfIn1 hpfOut hpfOut1 hq psi hA

/--
[bcProbW_eq_fibreMass_mul_condBcProbW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma bcProbW_eq_fibreMass_mul_condBcProbW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pf : Sym2 V -> Real}
  {q : Real}
  {F : Finset (Sym2 V)}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hpf : forall e, 0 < pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  bcProbW G C pf q omega = (∑ rho ∈ condFibre F omega, bcProbW G C pf q rho) * condBcProbW G C pf q F omega omega := by
-- proof
  apply StatMech.FK.bcProbW_eq_fibreMass_mul_condBcProbW G C Gin Gout iota bdryOut hpf hpf1 hq F omega

/--
[ocd_bcProbW_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_bcProbW_decompose_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 0 < q) :
-- imply
  (∑ rho, B.indicator (fun _ => (1 : Real)) rho * bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) = ∑ psi ∈ Finset.univ.filter (fun psi => ocd_outProj iota psi = psi), (∑ sigma ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi, bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) * (∑ rho, B.indicator (fun _ => (1 : Real)) rho * condBcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
-- proof
  apply StatMech.FK.ocd_bcProbW_decompose G C Gin Gout iota bdryOut hiota hpfOut hpfOut1 hq B

/--
[ocd_sum_fibreMassW_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_sum_fibreMassW_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 0 < q) :
-- imply
  (∑ psi ∈ Finset.univ.filter (fun psi => ocd_outProj iota psi = psi), ∑ sigma ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) iota) psi, bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q sigma) = 1 := by
-- proof
  apply StatMech.FK.ocd_sum_fibreMassW_eq_one G C Gin Gout iota bdryOut hiota hpfOut hpfOut1 hq

/--
[ocd_free_inner_dominated_bcProbW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_free_inner_dominated_bcProbW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW Gin ⊥ pfIn q omega) <= ∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho := by
-- proof
  apply StatMech.FK.ocd_free_inner_dominated_bcProbW G C Gin Gout iota bdryOut hiota hadjm hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hA

/--
[ocd_wired_inner_dominated_bcProbW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_wired_inner_dominated_bcProbW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {pfIn : Sym2 Vin -> Real}
  {pfOut : Sym2 Vout -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (hiota : Function.Injective iota)
  (hadjm : ocd_AdjMatch Gin Gout iota)
  (bdryIn : Vin -> Prop)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hwire : forall psi : ConfigSpace (Sym2 Vout), ocd_inducedWiring Gout iota bdryOut psi <= Lattice.boundaryCliqueGraph bdryIn)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * bcProbW Gout (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW Gin (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
-- proof
  apply StatMech.FK.ocd_wired_inner_dominated_bcProbW G C Gin Gout iota bdryOut hiota hadjm bdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hwire hA

/--
[ocd_latticeWired_inner_dominatedW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma ocd_latticeWired_inner_dominatedW_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {C : SimpleGraph V}
  [DecidableRel C.Adj]
  [Fintype Vin]
  [Fintype Vout]
  [DecidableEq Vin]
  [DecidableEq Vout]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  [DecidablePred bdryOut]
  {d : Nat}
  {Sin Sout : Set (Lattice.Site d)}
  [Fintype Sin]
  [Fintype Sout]
  [DecidablePred bdryOut]
  [DecidablePred bdryIn]
  {pfIn : Sym2 {y : Lattice.Site d // y ∈ Sin} -> Real}
  {pfOut : Sym2 {y : Lattice.Site d // y ∈ Sout} -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 {y : Lattice.Site d // y ∈ Sin}))}
-- given
  (iota : Vin -> Vout)
  (bdryOut : Vout -> Prop)
  (iota : {y : Lattice.Site d // y ∈ Sin} -> {y : Lattice.Site d // y ∈ Sout})
  (hiotaVal : forall x, (iota x : Lattice.Site d) = (x : Lattice.Site d))
  (hiota : Function.Injective iota)
  (bdryOut : {y : Lattice.Site d // y ∈ Sout} -> Prop)
  (bdryIn : {y : Lattice.Site d // y ∈ Sin} -> Prop)
  (hmargin : forall x : {y : Lattice.Site d // y ∈ Sin}, ¬ bdryOut (iota x))
  (hbdryIn : forall (x : {y : Lattice.Site d // y ∈ Sin}) (z : Lattice.Site d), Lattice.NearestNeighbour d (x : Lattice.Site d) z -> z ∉ Sin -> bdryIn x)
  (hparam : ocd_ParamCompatible iota pfIn pfOut)
  (hpfIn : forall e, 0 < pfIn e)
  (hpfIn1 : forall e, pfIn e < 1)
  (hpfOut : forall e, 0 < pfOut e)
  (hpfOut1 : forall e, pfOut e < 1)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho * bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)) (Lattice.boundaryCliqueGraph bdryOut) pfOut q rho) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW (SimpleGraph.comap Subtype.val (Lattice.hypercubicLattice d)) (Lattice.boundaryCliqueGraph bdryIn) pfIn q omega := by
-- proof
  apply StatMech.FK.ocd_latticeWired_inner_dominatedW G C Gin Gout iota bdryOut iota hiotaVal hiota bdryOut bdryIn hmargin hbdryIn hparam hpfIn hpfIn1 hpfOut hpfOut1 hq hA

/--
[weighted_transShellEvent_domain_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomain.lean)
-/
@[path]
private lemma weighted_transShellEvent_domain_dominated_eq
  {d R k : Nat}
  {x : Site d}
  {beta q : Real}
-- given
  (J : Sym2 (Site d) -> Real)
  (hJ : forall e, 0 < J e)
  (hsub : fvs_transBox d (2 * k) x ⊆ box d R)
  (hmargin : forall y : fvs_transBoxVerts d (2 * k) x, ¬ boxBoundary d R (flc_incl hsub y))
  (hk : 1 <= k)
  (hbeta : 0 < beta)
  (hq : 1 <= q) :
-- imply
  (∑ rho, (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator (fun _ => (1 : Real)) rho * bcProbW (boxGraph d R) (Lattice.boundaryCliqueGraph (boxBoundary d R)) (FK.betaParams (boxCoupling J R) beta) q rho) <= ∑ eta, (transShellEvent d k x).indicator (fun _ => (1 : Real)) eta * bcProbW (fvs_transBoxGraph d (2 * k) x) (Lattice.boundaryCliqueGraph (fvs_transBoxBoundary d (2 * k) x)) (FK.betaParams (transBoxCoupling J (2 * k) x) beta) q eta := by
-- proof
  apply StatMech.OSSS.FKSharpnessWeightedDomain.weighted_transShellEvent_domain_dominated d R k x J hJ hsub hmargin hk beta q hbeta hq


-- created on 2026-10-23

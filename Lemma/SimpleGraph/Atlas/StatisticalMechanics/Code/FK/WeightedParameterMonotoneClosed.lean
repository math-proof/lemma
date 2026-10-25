import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
open Finset Set StatMech StatMech.FK


/--
[edgeProductW_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma edgeProductW_nonneg_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V -> Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 <= pf e)
  (hpf1 : forall e, pf e < 1) :
-- imply
  0 <= edgeProductW G pf omega := by
-- proof
  apply StatMech.FK.edgeProductW_nonneg_of_nonneg G hpf hpf1 omega

/--
[bcWeightW_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcWeightW_nonneg_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 <= pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 <= bcWeightW G C pf q omega := by
-- proof
  apply StatMech.FK.bcWeightW_nonneg_of_nonneg G C hpf hpf1 hq omega

/--
[bcZW_pos_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcZW_pos_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
-- given
  (hpf : forall e, 0 <= pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 < bcZW G C pf q := by
-- proof
  apply StatMech.FK.bcZW_pos_of_nonneg G C hpf hpf1 hq

/--
[bcProbW_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcProbW_nonneg_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
  {omega : ConfigSpace (Sym2 V)}
-- given
  (hpf : forall e, 0 <= pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  0 <= bcProbW G C pf q omega := by
-- proof
  apply StatMech.FK.bcProbW_nonneg_of_nonneg G C hpf hpf1 hq omega

/--
[bcProbW_sum_eq_one_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcProbW_sum_eq_one_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf : Sym2 V -> Real}
  {q : Real}
-- given
  (hpf : forall e, 0 <= pf e)
  (hpf1 : forall e, pf e < 1)
  (hq : 0 < q) :
-- imply
  (∑ omega, bcProbW G C pf q omega) = 1 := by
-- proof
  apply StatMech.FK.bcProbW_sum_eq_one_of_nonneg G C hpf hpf1 hq

/--
[edgeProductW_cross_params_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma edgeProductW_cross_params_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hpf1 : forall e, 0 <= pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 <= pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e) :
-- imply
  edgeProductW G pf1 a * edgeProductW G pf2 b <= edgeProductW G pf1 (a ⊓ b) * edgeProductW G pf2 (a ⊔ b) := by
-- proof
  apply StatMech.FK.edgeProductW_cross_params_of_nonneg G hpf1 hpf1' hpf2 hpf2' hle a b

/--
[bcWeightW_cross_params_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcWeightW_cross_params_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {q : Real}
  {a b : ConfigSpace (Sym2 V)}
-- given
  (hpf1 : forall e, 0 <= pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 <= pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e)
  (hq : 1 <= q) :
-- imply
  bcWeightW G C pf1 q a * bcWeightW G C pf2 q b <= bcWeightW G C pf1 q (a ⊓ b) * bcWeightW G C pf2 q (a ⊔ b) := by
-- proof
  apply StatMech.FK.bcWeightW_cross_params_of_nonneg G C hpf1 hpf1' hpf2 hpf2' hle hq a b

/--
[bcProbW_mono_params_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WeightedParameterMonotoneClosed.lean)
-/
@[path]
private lemma bcProbW_mono_params_of_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G C : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel C.Adj]
  {pf1 pf2 : Sym2 V -> Real}
  {q : Real}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hpf1 : forall e, 0 <= pf1 e)
  (hpf1' : forall e, pf1 e < 1)
  (hpf2 : forall e, 0 <= pf2 e)
  (hpf2' : forall e, pf2 e < 1)
  (hle : forall e, pf1 e <= pf2 e)
  (hq : 1 <= q)
  (hA : IsIncreasing A) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C pf1 q omega) <= ∑ omega, A.indicator (fun _ => (1 : Real)) omega * bcProbW G C pf2 q omega := by
-- proof
  apply StatMech.FK.bcProbW_mono_params_of_nonneg G C hpf1 hpf1' hpf2 hpf2' hle hq hA


-- created on 2026-10-23

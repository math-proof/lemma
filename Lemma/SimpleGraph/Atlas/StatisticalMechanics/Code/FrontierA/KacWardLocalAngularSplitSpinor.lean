import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitSpinor
open StatMech StatMech.FrontierA


/--
[kwLocalPortRoot_sq_of_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalPortRoot_sq_of_matching_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {p q : KWDartPort G}
-- given
  (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
-- imply
  data.root q ^ 2 = -(data.root p ^ 2) := by
-- proof
  apply StatMech.FrontierA.kwLocalPortRoot_sq_of_matching data hmatching

/--
[kwLocalAngularSplitSpinorGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorGauge_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : (kwOrderedDartPortSplitGraph G (data.order)).Dart} :
-- imply
  kwLocalAngularSplitSpinorGauge data d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorGauge_ne_zero data d

/--
[kwLocalAngularSplitSpinorDirection_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorDirection_symm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : (kwOrderedDartPortSplitGraph G (data.order)).Dart} :
-- imply
  kwLocalAngularSplitSpinorDirection data d.symm = -kwLocalAngularSplitSpinorDirection data d := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorDirection_symm data d

/--
[kwLocalAngularSplitSpinorDirection_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorDirection_ne_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : (kwOrderedDartPortSplitGraph G (data.order)).Dart} :
-- imply
  kwLocalAngularSplitSpinorDirection data d ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorDirection_ne_zero data d

/--
[kwLocalAngularSplitSpinorPhase_sq_mul_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorPhase_sq_mul_direction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d e : (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  kwLocalAngularSplitSpinorPhase data d e ^ 2 * kwLocalAngularSplitSpinorDirection data d = kwLocalAngularSplitSpinorDirection data e := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorPhase_sq_mul_direction data d e hconnect hne

/--
[kwLocalAngularSplitSpinorPath_sq_mul_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorPath_sq_mul_direction_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {N : Nat}
  {path : Fin (N + 1) → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : ∀ j : Fin N, (path j.castSucc).snd = (path j.succ).fst ∧ (path j.castSucc).edge ≠ (path j.succ).edge) :
-- imply
  (∏ j : Fin N, kwLocalAngularSplitSpinorPhase data (path j.castSucc) (path j.succ)) ^ 2 * kwLocalAngularSplitSpinorDirection data (path 0) = kwLocalAngularSplitSpinorDirection data (path (Fin.last N)) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorPath_sq_mul_direction data path hvalid

/--
[kwLocalAngularSplitSpinorPath_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorPath_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {N : Nat}
  {path : Fin (N + 1) → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hend : path (Fin.last N) = (path 0).symm)
  (hvalid : ∀ j : Fin N, (path j.castSucc).snd = (path j.succ).fst ∧ (path j.castSucc).edge ≠ (path j.succ).edge) :
-- imply
  (∏ j : Fin N, kwLocalAngularSplitSpinorPhase data (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorPath_sq data path hend hvalid

/--
[kwLocalAngularSplitSpinorPhase_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorPhase_reverse_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d e : (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hconnect : d.snd = e.fst)
  (hne : d.edge ≠ e.edge) :
-- imply
  kwLocalAngularSplitSpinorPhase data e.symm d.symm = (kwLocalAngularSplitSpinorPhase data d e)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorPhase_reverse data d e hconnect hne

/--
[kwLocalAngularSplitSpinorLoop_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorLoop_sq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : ∀ k : Fin n, (loop k).snd = (loop (k + 1)).fst ∧ (loop k).edge ≠ (loop (k + 1)).edge) :
-- imply
  (∏ k : Fin n, kwLocalAngularSplitSpinorPhase data (loop k) (loop (k + 1))) ^ 2 = 1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorLoop_sq data loop hvalid

/--
[kwLocalAngularSplitGraphLoopWeight_surgery_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitGraphLoopWeight_surgery_sign_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {weight : Sym2 (KWDartPort G) → Complex}
  {selected : (kwOrderedDartPortSplitGraph G (data.order)).Dart}
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hboth : (∃ i, loop i = selected) ∧ ∃ j, loop j = selected.symm) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) weight (kwLocalAngularSplitSpinorPhase data)) (StatMech.Onsager.ons_surgery selected SimpleGraph.Dart.symm loop) = -StatMech.Onsager.ons_loopWeight (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) weight (kwLocalAngularSplitSpinorPhase data)) loop := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitGraphLoopWeight_surgery_sign data weight selected loop hboth

/--
[kwLocalAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {selected : (kwOrderedDartPortSplitGraph G (data.order)).Dart}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitSpinorPhase data)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinor_formalRoot_coeff_eq_zero_of_repeated data selected m hrepeated

/--
[kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_repeated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_repeated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {selected : (kwOrderedDartPortSplitGraph G (data.order)).Dart}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hrepeated : 2 ≤ m selected.edge) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitPhase data)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_repeated data selected m hrepeated

/--
[kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean)
-/
@[path]
private lemma kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {m : Sym2 (KWDartPort G) →₀ Nat}
-- given
  (hm : ¬StatMech.Onsager.ons_IsSquarefreeExponent m) :
-- imply
  MvPowerSeries.coeff m (kwGraphFormalRoot (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitPhase data)) = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree data m hm


-- created on 2026-10-23

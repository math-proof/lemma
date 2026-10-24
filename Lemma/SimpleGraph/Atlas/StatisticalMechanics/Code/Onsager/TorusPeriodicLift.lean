import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
open StatMech StatMech.Onsager


/--
[ons_pos_last_add_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_pos_last_add_step_eq
  {m : ℕ}
  {d : Fin (m + 1) → Fin 4} :
-- imply
  pos d (Fin.last m) + stepOf (d (Fin.last m)) = ∑ i, stepOf (d i) := by
-- proof
  apply StatMech.Onsager.ons_pos_last_add_step d

/--
[ons_liftDir_totalStep_eq_windingTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_liftDir_totalStep_eq_windingTranslation_eq
  {L n : ℕ}
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
-- imply
  ∑ k, stepOf (ons_liftDir v k) = ons_windingTranslation L mx my := by
-- proof
  apply StatMech.Onsager.ons_liftDir_totalStep_eq_windingTranslation v mx my hmx hmy

/--
[ons_periodicLiftVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_periodicLiftVertex_injective_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hne : mx ≠ 0 ∨ my ≠ 0) :
-- imply
  Function.Injective (fun z : ℤ × Fin n => ons_periodicLiftVertex v mx my z.1 z.2) := by
-- proof
  apply StatMech.Onsager.ons_periodicLiftVertex_injective v hvalid hsite mx my hne

/--
[ons_anchoredPeriodicLiftVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_anchoredPeriodicLiftVertex_injective_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hne : mx ≠ 0 ∨ my ≠ 0) :
-- imply
  Function.Injective (fun z : ℤ × Fin n => ons_anchoredPeriodicLiftVertex v mx my z.1 z.2) := by
-- proof
  apply StatMech.Onsager.ons_anchoredPeriodicLiftVertex_injective v hvalid hsite mx my hne

/--
[ons_reduceSite_anchoredPeriodicLiftVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_reduceSite_anchoredPeriodicLiftVertex_eq
  {L n : ℕ}
  [NeZero L]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx my r : ℤ}
  {i : Fin n}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1) :
-- imply
  ons_reduceSite L (ons_anchoredPeriodicLiftVertex v mx my r i) = ons_liftSite v i := by
-- proof
  apply StatMech.Onsager.ons_reduceSite_anchoredPeriodicLiftVertex v hvalid mx my r i

/--
[ons_anchoredPeriodicLiftVertex_ne_of_torus_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_anchoredPeriodicLiftVertex_ne_of_torus_disjoint_eq
  {L n m : ℕ}
  [NeZero L]
  [NeZero n]
  [NeZero m]
  {v : Fin n → ons_Dart L}
  {w : Fin m → ons_Dart L}
  {vmx vmy wmx wmy r s : ℤ}
  {i : Fin n}
  {j : Fin m}
-- given
  (hvvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hwvalid : ∀ k : Fin m, (w k).1 = ons_dirStep L (w (k + 1)).2 (w (k + 1)).1)
  (hdisj : ∀ i j, (v i).1 ≠ (w j).1) :
-- imply
  ons_anchoredPeriodicLiftVertex v vmx vmy r i ≠ ons_anchoredPeriodicLiftVertex w wmx wmy s j := by
-- proof
  apply StatMech.Onsager.ons_anchoredPeriodicLiftVertex_ne_of_torus_disjoint v w hvvalid hwvalid hdisj vmx vmy wmx wmy r s i j

/--
[ons_simpleLoop_nonzeroHomology_periodicLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_simpleLoop_nonzeroHomology_periodicLift_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k => (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hhom : ons_evenHomology L (ons_dartEdgeSet v) ≠ 0) :
-- imply
  ∃ mx my : ℤ, (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx ∧ (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my ∧ (mx ≠ 0 ∨ my ≠ 0) ∧ Function.Injective (fun z : ℤ × Fin n => ons_anchoredPeriodicLiftVertex v mx my z.1 z.2) := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_nonzeroHomology_periodicLift v hvalid hsite hnu hhom

/--
[ons_decCycles_anchoredPeriodicLifts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_decCycles_anchoredPeriodicLifts_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d e : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {p : (ons_decGraph L).Walk e e}
  {qmx qmy pmx pmy r s : ℤ}
  {i : Fin (ons_decExpandedDartList L q).length}
  {j : Fin (ons_decExpandedDartList L p).length}
-- given
  (hq : q.IsCycle)
  (hp : p.IsCycle)
  (hdisj : Disjoint q.toSubgraph.verts p.toSubgraph.verts) :
-- imply
  letI : NeZero (ons_decExpandedDartList L q).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩ letI : NeZero (ons_decExpandedDartList L p).length := ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L p hp)⟩ ons_anchoredPeriodicLiftVertex (ons_decExpandedKWLoop L q hq) qmx qmy r i ≠ ons_anchoredPeriodicLiftVertex (ons_decExpandedKWLoop L p hp) pmx pmy s j := by
-- proof
  apply StatMech.Onsager.ons_decCycles_anchoredPeriodicLifts_disjoint L q p hq hp hdisj qmx qmy pmx pmy r s i j

/--
[ons_periodicLiftVertex_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_periodicLiftVertex_step_eq
  {L m : ℕ}
  {v : Fin (m + 1) → ons_Dart L}
  {mx my r : ℤ}
  {i : Fin m} :
-- imply
  ons_periodicLiftVertex v mx my r i.succ = ons_periodicLiftVertex v mx my r i.castSucc + stepOf (ons_liftDir v i.castSucc) := by
-- proof
  apply StatMech.Onsager.ons_periodicLiftVertex_step v mx my r i

/--
[ons_periodicLiftVertex_last_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPeriodicLift.lean)
-/
@[path]
private lemma ons_periodicLiftVertex_last_step_eq
  {L m : ℕ}
  {v : Fin (m + 1) → ons_Dart L}
  {mx my r : ℤ}
-- given
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = (L : ℤ) * my) :
-- imply
  ons_periodicLiftVertex v mx my (r + 1) 0 = ons_periodicLiftVertex v mx my r (Fin.last m) + stepOf (ons_liftDir v (Fin.last m)) := by
-- proof
  apply StatMech.Onsager.ons_periodicLiftVertex_last_step v mx my r hmx hmy


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
open StatMech StatMech.FrontierA


/--
[kwLocalAngularSplitPhase_external_internal_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_external_internal_of_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hrank : kwOrderedPortRank (data.order) e.1.fst < kwOrderedPortRank (data.order) e.1.snd) :
-- imply
  kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 e.1 = -Complex.I * (data.root e.1.fst)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_external_internal_of_rank_lt data d e hrank

/--
[kwLocalAngularSplitPhase_external_internal_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_external_internal_of_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hrank : kwOrderedPortRank (data.order) e.1.snd < kwOrderedPortRank (data.order) e.1.fst) :
-- imply
  kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 e.1 = Complex.I * (data.root e.1.fst)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_external_internal_of_rank_gt data d e hrank

/--
[kwLocalAngularSplitPhase_internal_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_internal_external_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart} :
-- imply
  kwLocalAngularSplitPhase data d.1 (kwOrderedExternalSplitDartOfDart G (data.order) e).1 = data.root (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_internal_external data d e

/--
[kwLocalAngularSplitPhase_internal_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_internal_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d e : KWOrderedInternalSplitDart G (data.order)} :
-- imply
  kwLocalAngularSplitPhase data d.1 e.1 = 1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_internal_internal data d e

/--
[kwLocalAngularSplitPhase_endpointProduct_of_rank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_endpointProduct_of_rank_lt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d e : G.Dart}
  {first last : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (data.order) (kwPortOfDart G d.symm) < kwOrderedPortRank (data.order) (kwPortOfDart G e))
  (hfirst : first.1.fst = kwPortOfDart G d.symm)
  (hfirstRank : kwOrderedPortRank (data.order) first.1.fst < kwOrderedPortRank (data.order) first.1.snd) :
-- imply
  kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 first.1 * kwLocalAngularSplitPhase data last.1 (kwOrderedExternalSplitDartOfDart G (data.order) e).1 = data.phase d e := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_endpointProduct_of_rank_lt data d e hde hrank first last hfirst hfirstRank

/--
[kwLocalAngularSplitPhase_endpointProduct_of_rank_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitPhase_endpointProduct_of_rank_gt_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d e : G.Dart}
  {first last : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hde : d.snd = e.fst)
  (hrank : kwOrderedPortRank (data.order) (kwPortOfDart G e) < kwOrderedPortRank (data.order) (kwPortOfDart G d.symm))
  (hfirst : first.1.fst = kwPortOfDart G d.symm)
  (hfirstRank : kwOrderedPortRank (data.order) first.1.snd < kwOrderedPortRank (data.order) first.1.fst) :
-- imply
  kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 first.1 * kwLocalAngularSplitPhase data last.1 (kwOrderedExternalSplitDartOfDart G (data.order) e).1 = data.phase d e := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitPhase_endpointProduct_of_rank_gt data d e hde hrank first last hfirst hfirstRank

/--
[kwLocalAngularSplit_internalPhase_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internalPhase_eq_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G} :
-- imply
  kwOrderedInternalPhase G (data.order) (kwLocalAngularSplitPhase data) = fun _ _ ↦ 1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internalPhase_eq_one data

/--
[kwLocalAngularSplit_internalBlock_apply_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internalBlock_apply_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hstep : KWOrderedInternalDartStep G (data.order) d e) :
-- imply
  kwOrderedSplitInternalBlock G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e = 1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internalBlock_apply_of_step data weight d e hstep

/--
[kwLocalAngularSplit_internalBlock_apply_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internalBlock_apply_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hstep : ¬KWOrderedInternalDartStep G (data.order) d e) :
-- imply
  kwOrderedSplitInternalBlock G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internalBlock_apply_of_not_step data weight d e hstep

/--
[kwLocalAngularSplit_enterBlock_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_enterBlock_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hconnect : kwPortOfDart G d.symm = e.1.fst) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e = weight d.edge * kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 e.1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_enterBlock_apply_of_connect data weight d e hconnect

/--
[kwLocalAngularSplit_enterBlock_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_enterBlock_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))).toBlocks₁₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_enterBlock_apply_of_not_connect data weight d e hconnect

/--
[kwLocalAngularSplit_exitBlock_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_exitBlock_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd = kwPortOfDart G e) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e = data.root (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_exitBlock_apply_of_connect data weight d e hconnect

/--
[kwLocalAngularSplit_exitBlock_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_exitBlock_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  (kwOrderedSplitTransitionInBlocks G (data.order) (kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data))).toBlocks₂₁ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_exitBlock_apply_of_not_connect data weight d e hconnect

/--
[kwLocalAngularSplitBlocks_internal_apply_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_internal_apply_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hstep : KWOrderedInternalDartStep G (data.order) d e) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_internal_apply_of_step data weight d e hstep

/--
[kwLocalAngularSplitBlocks_internal_apply_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_internal_apply_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hstep : ¬KWOrderedInternalDartStep G (data.order) d e) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_internal_apply_of_not_step data weight d e hstep

/--
[kwLocalAngularSplitBlocks_enter_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_enter_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hconnect : kwPortOfDart G d.symm = e.1.fst) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e = weight d.edge * kwLocalAngularSplitPhase data (kwOrderedExternalSplitDartOfDart G (data.order) d).1 e.1 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_enter_apply_of_connect data weight d e hconnect

/--
[kwLocalAngularSplitBlocks_enter_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_enter_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : G.Dart}
  {e : KWOrderedInternalSplitDart G (data.order)}
-- given
  (hconnect : kwPortOfDart G d.symm ≠ e.1.fst) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_enter_apply_of_not_connect data weight d e hconnect

/--
[kwLocalAngularSplitBlocks_exit_apply_of_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_exit_apply_of_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd = kwPortOfDart G e) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e = data.root (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_exit_apply_of_connect data weight d e hconnect

/--
[kwLocalAngularSplitBlocks_exit_apply_of_not_connect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplitBlocks_exit_apply_of_not_connect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hconnect : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitBlocks_exit_apply_of_not_connect data weight d e hconnect

/--
[kwLocalAngularInternalExitSolution_of_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularInternalExitSolution_of_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hfaces : KWOrderedInternalDartFacesPort (data.order) d (kwPortOfDart G e)) :
-- imply
  kwLocalAngularInternalExitSolution data d e = data.root (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularInternalExitSolution_of_faces data d e hfaces

/--
[kwLocalAngularInternalExitSolution_of_not_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularInternalExitSolution_of_not_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hfaces : ¬KWOrderedInternalDartFacesPort (data.order) d (kwPortOfDart G e)) :
-- imply
  kwLocalAngularInternalExitSolution data d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularInternalExitSolution_of_not_faces data d e hfaces

/--
[kwLocalAngularSplit_internal_mul_exitSolution_of_faces_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internal_mul_exitSolution_of_faces_of_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hfaces : KWOrderedInternalDartFacesPort (data.order) d (kwPortOfDart G e))
  (hne : d.1.snd ≠ kwPortOfDart G e) :
-- imply
  ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ * kwLocalAngularInternalExitSolution data) d e = data.root (kwPortOfDart G e) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internal_mul_exitSolution_of_faces_of_ne data weight d e hfaces hne

/--
[kwLocalAngularSplit_internal_mul_exitSolution_of_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internal_mul_exitSolution_of_snd_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hsnd : d.1.snd = kwPortOfDart G e) :
-- imply
  ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ * kwLocalAngularInternalExitSolution data) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internal_mul_exitSolution_of_snd_eq data weight d e hsnd

/--
[kwLocalAngularSplit_internal_mul_exitSolution_of_not_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_internal_mul_exitSolution_of_not_faces_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d : KWOrderedInternalSplitDart G (data.order)}
  {e : G.Dart}
-- given
  (hfaces : ¬KWOrderedInternalDartFacesPort (data.order) d (kwPortOfDart G e)) :
-- imply
  ((kwLocalAngularSplitBlocks data weight).toBlocks₂₂ * kwLocalAngularInternalExitSolution data) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_internal_mul_exitSolution_of_not_faces data weight d e hfaces

/--
[kwLocalAngularSplit_exitSolution_equation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_exitSolution_equation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ} :
-- imply
  (1 - (kwLocalAngularSplitBlocks data weight).toBlocks₂₂) * kwLocalAngularInternalExitSolution data = (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_exitSolution_equation data weight

/--
[kwLocalAngularSplit_resolvent_mul_exit_eq_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_resolvent_mul_exit_eq_solution_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {n : ℕ}
-- given
  (hpow : (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ ^ n = 0) :
-- imply
  kwNilpotentResolvent (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n * (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ = kwLocalAngularInternalExitSolution data := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_resolvent_mul_exit_eq_solution data weight n hpow

/--
[kwLocalAngularSplit_enter_mul_exitSolution_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_enter_mul_exitSolution_of_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : G.Dart}
-- given
  (hde : d.snd = e.fst)
  (hnb : d.edge ≠ e.edge) :
-- imply
  ((kwLocalAngularSplitBlocks data weight).toBlocks₁₂ * kwLocalAngularInternalExitSolution data) d e = weight d.edge * data.phase d e := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_enter_mul_exitSolution_of_step data weight d e hde hnb

/--
[kwLocalAngularSplit_enter_mul_exitSolution_of_not_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_enter_mul_exitSolution_of_not_step_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {d e : G.Dart}
-- given
  (hstep : ¬(d.snd = e.fst ∧ d.edge ≠ e.edge)) :
-- imply
  ((kwLocalAngularSplitBlocks data weight).toBlocks₁₂ * kwLocalAngularInternalExitSolution data) d e = 0 := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_enter_mul_exitSolution_of_not_step data weight d e hstep

/--
[kwLocalAngularSplit_enter_mul_exitSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_enter_mul_exitSolution_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ} :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ * kwLocalAngularInternalExitSolution data = kwGraphTransition G weight data.phase := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_enter_mul_exitSolution data weight

/--
[kwLocalAngularSplit_pathEffective_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_pathEffective_eq_original_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ}
  {n : ℕ}
-- given
  (hpow : (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ ^ n = 0) :
-- imply
  (kwLocalAngularSplitBlocks data weight).toBlocks₁₂ * kwNilpotentResolvent (kwLocalAngularSplitBlocks data weight).toBlocks₂₂ n * (kwLocalAngularSplitBlocks data weight).toBlocks₂₁ = kwGraphTransition G weight data.phase := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_pathEffective_eq_original data weight n hpow

/--
[kwLocalAngularSplit_det_eq_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean)
-/
@[path]
private lemma kwLocalAngularSplit_det_eq_original_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {weight : Sym2 V → ℂ} :
-- imply
  (1 - kwGraphTransition (kwOrderedDartPortSplitGraph G (data.order)) (kwOrderedSplitWeight G weight) (kwLocalAngularSplitPhase data)).det = (1 - kwGraphTransition G weight data.phase).det := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_det_eq_original data weight


-- created on 2026-10-23

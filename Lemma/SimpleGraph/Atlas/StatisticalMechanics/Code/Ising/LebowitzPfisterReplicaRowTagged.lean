import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowCopies_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowCopies_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectTag G sites m tag) row = lpReplicaReflectCopies G sites m (lpReplicaRowCopies G sites m tag row) := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_reflectTag G sites m tag row

/--
[lpReplicaCurrentCopies_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCurrentCopies G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectTag G sites m tag) row current = lpReplicaReflectCopies G sites m (lpReplicaCurrentCopies G sites m tag row current) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_reflectTag G sites m tag row current

/--
[lpReplicaCurrentSources_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCurrentSources_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaCurrentCopies G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectTag G sites m tag) row current) = (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag row current)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentSources_reflectTag G sites m tag row current

/--
[lpReplicaRowConn_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowConn_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {row : Bool}
  {a b : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) (lpReplicaRowCopies G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectTag G sites m tag) row) (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag row) a b := by
-- proof
  apply StatMech.Ising.lpReplicaRowConn_reflectTag G sites m tag row a b

/--
[lpReplicaCollision_origin_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_origin_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Disjoint ((Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) a)).map (lpReplicaCollisionLeftCopyEmbedding G sites a b)) ((Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) b)).map (lpReplicaCollisionRightCopyEmbedding G sites a b)) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_origin_disjoint G sites a b

/--
[lpReplicaCollision_origin_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_origin_union_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) a)).map (lpReplicaCollisionLeftCopyEmbedding G sites a b) ∪ (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) b)).map (lpReplicaCollisionRightCopyEmbedding G sites a b) = Finset.univ := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_origin_union G sites a b

/--
[lpReplicaCollision_rightOrigin_eq_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_rightOrigin_eq_sdiff_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) b)).map (lpReplicaCollisionRightCopyEmbedding G sites a b) = Finset.univ \ ((Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) a)).map (lpReplicaCollisionLeftCopyEmbedding G sites a b)) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_rightOrigin_eq_sdiff G sites a b

/--
[lpReplicaCollision_currentCopies_left_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_currentCopies_left_false_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) false false = Sa.map (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_currentCopies_left_false G sites a b Sa Sb

/--
[lpReplicaCollision_currentCopies_left_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_currentCopies_left_true_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) false true = ((Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) a)) \ Sa).map (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_currentCopies_left_true G sites a b Sa Sb

/--
[lpReplicaCollision_currentCopies_right_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_currentCopies_right_false_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) true false = Sb.map (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_currentCopies_right_false G sites a b Sa Sb

/--
[lpReplicaCollision_currentCopies_right_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_currentCopies_right_true_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) true true = ((Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) b)) \ Sb).map (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_currentCopies_right_true G sites a b Sa Sb

/--
[lpReplicaCollision_rowCopies_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_rowCopies_false_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) false = (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) a)).map (lpReplicaCollisionLeftCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_rowCopies_false G sites a b Sa Sb

/--
[lpReplicaCollision_rowCopies_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_rowCopies_true_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) true = (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) b)).map (lpReplicaCollisionRightCopyEmbedding G sites a b) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_rowCopies_true G sites a b Sa Sb

/--
[lpReplicaCollision_leftSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_leftSources_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
  {current : Bool}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a b)) (lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) false current) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) a) (if current then Finset.univ \ Sa else Sa) := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_leftSources G sites a b Sa Sb current

/--
[lpReplicaCollision_rightSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollision_rightSources_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
  {current : Bool}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites a b)) (lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites a b) (lpReplicaCollisionRowTag G sites a b Sa Sb) true current) = (RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) b) (if current then Finset.univ \ Sb else Sb)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaCollision_rightSources G sites a b Sa Sb current

/--
[lpReplicaToggleRows_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaToggleRows_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaToggleRows G sites m P) := by
-- proof
  apply StatMech.Ising.lpReplicaToggleRows_involutive G sites m P

/--
[lpReplicaRowCopies_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowCopies_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) row = lpReplicaRowCopies G sites m tag row ∆ P := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_toggle G sites m P tag row

/--
[lpReplicaCurrentCopies_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaToggleRows G sites m P tag) row current = lpReplicaCurrentCopies G sites m tag row current ∆ P.filter (fun c => (tag c).2 = current) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_toggle G sites m P tag row current

/--
[lpReplicaCurrentCopies_subset_rowCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_subset_rowCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCurrentCopies G sites m tag row current ⊆ lpReplicaRowCopies G sites m tag row := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_subset_rowCopies G sites m tag row current

/--
[lpReplicaRowCopies_eq_current_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowCopies_eq_current_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites m tag row = lpReplicaCurrentCopies G sites m tag row false ∆ lpReplicaCurrentCopies G sites m tag row true := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_eq_current_symmDiff G sites m tag row

/--
[lpReplicaRowSources_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowSources_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) row) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag row) ∆ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) P := by
-- proof
  apply StatMech.Ising.lpReplicaRowSources_toggle G sites m P tag row

/--
[lpReplicaCurrentSources_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCurrentSources_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m (lpReplicaToggleRows G sites m P tag) row current) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag row current) ∆ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (P.filter (fun c => (tag c).2 = current)) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentSources_toggle G sites m P tag row current

/--
[lpReplicaRowSources_eq_currentSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowSources_eq_currentSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag row) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag row false) ∆ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag row true) := by
-- proof
  apply StatMech.Ising.lpReplicaRowSources_eq_currentSources G sites m tag row

/--
[lpReplicaRowComponent_root_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowComponent_root_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  root ∈ lpReplicaRowComponent G sites m tag row root := by
-- proof
  apply StatMech.Ising.lpReplicaRowComponent_root_mem G sites m tag row root

/--
[lpReplicaRowComponent_ghost1_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowComponent_ghost1_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hdisc : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag row) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ lpReplicaRowComponent G sites m tag row lpReplicaCurrentGhost0 := by
-- proof
  apply StatMech.Ising.lpReplicaRowComponent_ghost1_not_mem G sites m tag row hdisc

/--
[lpReplicaRowComponent_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowComponent_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {row : Bool}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowComponent G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaReflectTag G sites m tag) row (lpReplicaCurrentReflect root) = (lpReplicaRowComponent G sites m tag row root).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaRowComponent_reflectTag G sites m tag row root

/--
[lpReplicaCollisionRowGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaCollisionRowGate_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hSa : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) a) Sa = A)
  (hSa' : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) a) (Finset.univ \ Sa) = ∅)
  (hda : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) a) Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  (hSb : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) b) Sb = B)
  (hSb' : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) b) (Finset.univ \ Sb) = ∅)
  (hdb : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) b) Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites a b) A (B.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionRowGate G sites a b Sa Sb A B hSa hSa' hda hSb hSb' hdb

/--
[lpReplicaRowGate_reflectTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowGate_reflectTag_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  LPReplicaRowGate G sites (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) (A.map lpReplicaCurrentReflect.toEmbedding) (B.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaReflectTag G sites m tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_reflectTag G sites m A B tag hgate

/--
[lpReplicaRowGate_rowSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowGate_rowSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag false) = A ∧ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m tag true) = B := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_rowSources G sites m A B tag hgate

/--
[lpReplicaRowGate_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowGate_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag)
  (hsecond : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (P.filter (fun c => (tag c).2 = true)) = ∅)
  (hdisc0 : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  (hdisc1 : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let X := RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (P.filter (fun c => (tag c).2 = false)) LPReplicaRowGate G sites m (A ∆ X) (B ∆ X) (lpReplicaToggleRows G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_toggle G sites m A B tag P hgate hsecond hdisc0 hdisc1

/--
[lpReplicaRowGate_toggle_offdiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean)
-/
@[path]
private lemma lpReplicaRowGate_toggle_offdiag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T : Finset (LPReplicaCurrentVertex V)}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m (Si ∆ Sj ∆ T) ∅ tag)
  (hfirst : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (P.filter (fun c => (tag c).2 = false)) = Sj ∆ T)
  (hsecond : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (P.filter (fun c => (tag c).2 = true)) = ∅)
  (hdisc0 : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  (hdisc1 : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m (lpReplicaToggleRows G sites m P tag) true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  LPReplicaRowGate G sites m Si (Sj ∆ T) (lpReplicaToggleRows G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_toggle_offdiag G sites m Si Sj T tag P hgate hfirst hsecond hdisc0 hdisc1


-- created on 2026-10-23

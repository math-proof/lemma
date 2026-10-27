import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectListFlatMapReplicate
open StatMech StatMech.FrontierD


/--
[fkRectList_flatMap_replicate_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectListFlatMapReplicate.lean)
-/
@[path]
private lemma fkRectList_flatMap_replicate_length_eq
  {alpha : Type}
  {l : List alpha}
  {scale : alpha → ℕ} :
-- imply
  (l.flatMap (fun a => List.replicate (scale a) a)).length = ∑ i : Fin l.length, scale (l.get i) := by
-- proof
  apply StatMech.FrontierD.fkRectList_flatMap_replicate_length l scale

/--
[fkRectList_get_flatMap_replicate_finSigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectListFlatMapReplicate.lean)
-/
@[path]
private lemma fkRectList_get_flatMap_replicate_finSigma_eq
  {alpha : Type}
  {l : List alpha}
  {scale : alpha → ℕ}
  {i : Fin l.length}
  {r : Fin (scale (l.get i))}
-- given
  (k : Fin (l.flatMap (fun a => List.replicate (scale a) a)).length)
  (hk : k.val = (finSigmaFinEquiv (⟨i, r⟩ : Σ i : Fin l.length, Fin (scale (l.get i)))).val) :
-- imply
  (l.flatMap (fun a => List.replicate (scale a) a)).get k = l.get i := by
-- proof
  apply StatMech.FrontierD.fkRectList_get_flatMap_replicate_finSigma l scale i r k hk


-- created on 2026-10-23

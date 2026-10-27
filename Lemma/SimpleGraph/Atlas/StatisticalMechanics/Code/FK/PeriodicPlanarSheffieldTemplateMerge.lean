import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTemplateMerge
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTemplateMerge.lean)
-/
@[path]
private lemma exists_uniform_translatedTemplate_mergeError_tendsto_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  [Fintype ι]
  [DecidableEq ι]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (L : Nat -> Finset V)
  (R : Nat -> ι -> Finset V) :
-- imply
  ∃ radius : Nat -> Nat, (∀ n, n ≤ radius n) ∧ ∀ (z : Nat -> Site 2) (i : Nat -> ι) (a b c d : Nat -> Real), (∀ n, (P.shift (z n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) ((L n).image (P.shift (z n))) ((R n (i n)).image (P.shift (z n))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniform_translatedTemplate_mergeError_tendsto_zero E mu hTI hunique L R


-- created on 2026-10-23

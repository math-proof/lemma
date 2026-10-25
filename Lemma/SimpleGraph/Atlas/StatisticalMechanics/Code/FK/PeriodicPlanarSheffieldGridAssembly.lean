import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldGridAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_uniformRadius_gridPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldGridAssembly.lean)
-/
@[path]
private lemma exists_uniformRadius_gridPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  exists radius : Nat -> Nat, forall (width height : Nat -> Nat) (hwidth : forall n, 0 < width n) (base : Nat -> Site 2) (vertical : (n : Nat) -> PreferenceGridVertex (width n) (height n) -> Bool) (horizontal : (n : Nat) -> PreferenceGridVertex (width n) (height n) -> Bool) (a b c d : Nat -> Real), (forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) -> (forall n i, vertical n (i, 0) = true) -> (forall n i, vertical n (i, Fin.last (height n)) = false) -> (forall n j, horizontal n (0, j) = true) -> (forall n j, horizontal n (Fin.last (width n), j) = false) -> (forall n v, vertical n v = true -> E.BottomPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) -> (forall n v, vertical n v = false -> E.TopPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) -> (forall n v, horizontal n v = true -> E.LeftPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) -> (forall n v, horizontal n v = false -> E.RightPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) -> Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformRadius_gridPreference_crossing_max_tendsto_one E mu hFKG hTI hunique


-- created on 2026-10-23

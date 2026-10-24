import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldTemplateGridAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_approxPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldTemplateGridAssembly.lean)
-/
@[path]
private lemma exists_uniformTemplate_approxPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat → Finset V}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height : Nat → Nat) (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n) (base : Nat → Site 2) (a b c d epsilon : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n (i : Fin (width n + 1)), top n (i, 0) ≤ bottom n (i, 0) + epsilon n) → (∀ n (i : Fin (width n + 1)), bottom n (i, Fin.last (height n)) ≤ top n (i, Fin.last (height n)) + epsilon n) → (∀ n (j : Fin (height n + 1)), right n (0, j) ≤ left n (0, j) + epsilon n) → (∀ n (j : Fin (height n + 1)), left n (Fin.last (width n), j) ≤ right n (Fin.last (width n), j) + epsilon n) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_approxPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit


-- created on 2026-10-23

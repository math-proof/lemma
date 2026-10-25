import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepTemplateGridAssembly.lean)
-/
@[path]
private lemma exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one_eq
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
  ∃ radius : Nat → Nat, ∀ (width height margin : Nat → Nat) (hwidth : ∀ n, 0 < width n) (base : Nat → Site 2) (vertical horizontal : (n : Nat) → PreferenceGridVertex (width n) (height n) → Bool) (a b c d epsilon : Nat → Real) (bottom top left right : (n : Nat) → PreferenceGridVertex (width n) (height n) → Real), Tendsto epsilon atTop (nhds 0) → (∀ n, 0 ≤ epsilon n) → (∀ n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n (v : PreferenceGridVertex (width n) (height n)), margin n ≤ v.1.val → v.1.val + margin n < width n → margin n ≤ v.2.val → v.2.val + margin n < height n → (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, bottom n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, top n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, left n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, right n v = mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) → (∀ n v, v.2.val ≤ margin n → vertical n v = true) → (∀ n v, height n ≤ v.2.val + margin n → vertical n v = false) → (∀ n v, v.1.val ≤ margin n → horizontal n v = true) → (∀ n v, width n ≤ v.1.val + margin n → horizontal n v = false) → (∀ n v, vertical n v = true → top n v ≤ bottom n v + epsilon n) → (∀ n v, vertical n v = false → bottom n v ≤ top n v + epsilon n) → (∀ n v, horizontal n v = true → right n v ≤ left n v + epsilon n) → (∀ n v, horizontal n v = false → left n v ≤ right n v + epsilon n) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit


-- created on 2026-10-23

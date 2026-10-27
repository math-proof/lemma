import Mathlib
import Initialize.Tactic.Attr.Basic
open Filter Set Topology
open scoped RestrictedProduct


/--
[proposition_25_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop256.lean)
-/
@[path]
lemma proposition_25_6
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  [∀ i, WeaklyLocallyCompactSpace (X i)]
  {U : (i : ι) → Set (X i)}
-- given
  (hU_open : ∀ i, IsOpen (U i))
  (hU_compact : ∀ᶠ i in cofinite, IsCompact (U i)) :
-- imply
  WeaklyLocallyCompactSpace (Πʳ i, [X i, U i]) :=
-- proof
  RestrictedProduct.weaklyLocallyCompactSpace_of_cofinite hU_open hU_compact


-- created on 2026-10-23

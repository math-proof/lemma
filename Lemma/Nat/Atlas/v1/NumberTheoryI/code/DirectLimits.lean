import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.DirectLimits.Part2
open TopologicalSpace TopologicalSpace.DirectLimit


namespace TopologicalSpace.DirectLimit

/--
[of_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean)
-/
@[path]
lemma of_continuous
  {ι : Type*}
  [Preorder ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {f : ∀ i j, i ≤ j → X i → X j}
  {i : ι} :
-- imply
  Continuous (of X f i) :=
-- proof
  continuous_quotient_mk'.comp continuous_sigmaMk

end TopologicalSpace.DirectLimit

namespace TopologicalSpace.DirectLimit

/--
[of_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean)
-/
@[path]
lemma of_comp
  {ι : Type*}
  [Preorder ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {f : ∀ i j, i ≤ j → X i → X j}
  {i j : ι}
  {x : X i}
-- given
  (h : i ≤ j) :
-- imply
  of X f j (f i j h x) = of X f i x := by
-- proof
  apply @Quotient.sound' _ (directLimitSetoid X f)
  exact (Relation.EqvGen.rel _ _ ⟨i, j, h, x, rfl, rfl⟩).symm

end TopologicalSpace.DirectLimit

namespace TopologicalSpace.DirectLimit

/--
[lift_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirectLimits.lean)
-/
@[path]
lemma lift_continuous
  {ι : Type*}
  [Preorder ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {f : ∀ i j, i ≤ j → X i → X j}
  {Y : Type*}
  [TopologicalSpace Y]
-- given
  (ψ : ∀ i, X i → Y)
  (hψ_cont : ∀ i, Continuous (ψ i))
  (hψ_comp : ∀ i j (h : i ≤ j) (x : X i), ψ j (f i j h x) = ψ i x) :
-- imply
  Continuous (lift X f ψ hψ_comp) := by
-- proof
  unfold lift
  exact (continuous_sigma fun i => hψ_cont i).quotient_lift _

end TopologicalSpace.DirectLimit


-- created on 2026-10-23
-- updated on 2026-10-29

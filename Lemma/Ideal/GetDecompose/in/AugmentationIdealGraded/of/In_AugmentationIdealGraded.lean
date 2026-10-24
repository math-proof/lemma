import Mathlib
import sympy.Basic
import Lemma.Ideal.IsHomogeneous_AugmentationIdealGraded
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
Graded components of an element of the graded augmentation ideal stay in that ideal
(atlas ugmentationIdealGraded_component_mem).

[augmentationIdealGraded_component_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [CommRing k]
  [CommRing S]
  [Algebra k S]
  {𝒮 : ℕ → Submodule k S}
  [GradedAlgebra 𝒮]
  {r : S}
  {j : ℕ}
-- given
  (hr : r ∈ Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S))) :
-- imply
  ((DirectSum.decompose 𝒮 r) j : S) ∈ Ideal.span (⋃ (i : ℕ) (_ : 0 < i), (𝒮 i : Set S)) :=
-- proof
  ((Ideal.IsHomogeneous_AugmentationIdealGraded (𝒮 := 𝒮)).mem_iff.mp hr) j


-- created on 2026-10-24

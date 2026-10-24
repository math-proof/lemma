import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.Faces
import sympy.atlas.v1.Atlas.Buildings.code.AffineCoxeter.AffineCriterion
open Finset BigOperators CoxeterGroup TitsCone AffineCoxeterFaces


namespace AffineCoxeterFaces

/--
[zero_not_mem_affineHyperplane](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/Faces.lean)
-/
@[path]
private lemma zero_not_mem_affineHyperplane
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B}
  {v₀ : B → ℝ}
-- given
  (_ : ∀ s, v₀ s > 0) :
-- imply
  (0 : B → ℝ) ∉ affineHyperplane M v₀ := by
-- proof
  intro h
  simp only [affineHyperplane, Set.mem_ofPred_eq] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  linarith

end AffineCoxeterFaces

namespace AffineCoxeterFaces

/--
[ne_zero_of_mem_affineHyperplane](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/Faces.lean)
-/
@[path]
private lemma ne_zero_of_mem_affineHyperplane
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B}
  {v₀ x : B → ℝ}
-- given
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hx : x ∈ affineHyperplane M v₀) :
-- imply
  x ≠ 0 := by
-- proof
  intro heq
  rw [heq] at hx
  exact zero_not_mem_affineHyperplane hv₀_pos hx

end AffineCoxeterFaces

namespace AffineCoxeterFaces

/--
[mem_titsCone_sdiff_zero_of_mem_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/Faces.lean)
-/
@[path]
private lemma mem_titsCone_sdiff_zero_of_mem_E
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {v₀ x : B → ℝ}
-- given
  (hAff : IsAffineCoxeter M)
  (hv₀_pos : ∀ s, v₀ s > 0)
  (hv₀_rad : ∀ t : B, ∑ u : B, v₀ u * formVal M u t = 0)
  (hx : x ∈ affineHyperplane M v₀) :
-- imply
  x ∈ titsConeSet M \ {0} := by
-- proof
  refine Set.mem_sdiff_singleton.mpr ⟨?_, ne_zero_of_mem_affineHyperplane hv₀_pos hx⟩
  obtain ⟨p₁, p₂, t, hp₁, hp₂, ht0, ht1, hxt⟩ :=
    ChamberChasingProperty.orbit_density v₀ hv₀_pos hv₀_rad hAff x hx
  have h1t : 0 ≤ 1 - t := by linarith
  have hab : (1 - t) + t = 1 := by ring
  have hconv := titsConeSet_convex M hp₁ hp₂ h1t ht0 hab
  convert hconv using 1
  ext s
  simp [hxt s]

end AffineCoxeterFaces


-- created on 2026-10-23
-- updated on 2026-10-24

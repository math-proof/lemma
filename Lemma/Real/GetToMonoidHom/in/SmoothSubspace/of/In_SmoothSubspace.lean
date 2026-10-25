import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.SmoothVectors
open ContinuousRep
open scoped Manifold


namespace ContinuousRep

/--
[smoothSubspace_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SmoothVectors.lean)
-/
@[path]
private lemma smoothSubspace_invariant
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F}
  {v : F}
-- given
  (h : G)
  (hv : v ∈ π.smoothSubspace I) :
-- imply
  (π.toMonoidHom h) v ∈ π.smoothSubspace I := by
-- proof
  simp only [smoothSubspace, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq] at *
  unfold IsSmoothVector orbitMap at *
  have heq : (fun g : G => (π.toMonoidHom g) ((π.toMonoidHom h) v)) =
    (fun g : G => (π.toMonoidHom g) v) ∘ (fun g => g * h) := by
    ext g; simp [map_mul]
  rw [heq]
  exact hv.comp (contMDiff_id.mul contMDiff_const)

end ContinuousRep


-- created on 2026-10-23
-- updated on 2026-10-24

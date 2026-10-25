import Mathlib
import sympy.Basic
import Def.Geometry.Manifold.ImmersionComp
open scoped Topology ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.ImmersionCompWanted


namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompEquiv_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompEquiv_apply_zero {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  (e₁ : (E × F₁) ≃L[𝕜] E'') (e₂ : (E'' × F₂) ≃L[𝕜] E''') (z : E) :
  immersionCompEquiv e₁ e₂ (z, 0) = e₂ (e₁ (z, 0), 0) := by
  rw [show (0 : F₁ × F₂) = (0, 0) by rfl]
  change e₂ ((e₁.prodCongr (ContinuousLinearEquiv.refl 𝕜 F₂))
    ((ContinuousLinearEquiv.prodAssoc 𝕜 E F₁ F₂).symm (z, (0, 0)))) = _
  rw [ContinuousLinearEquiv.prodAssoc_symm_apply]
  rfl

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_apply [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G) (z : E'') :
  immersionCompCoordChange (J := J) e e' z = J.extendCoordChange e e' z := by
  simp [immersionCompCoordChange, ModelWithCorners.extendCoordChange, Function.comp_def]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_source](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_source [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G) :
  (immersionCompCoordChange (J := J) e e').source = (J.extendCoordChange e e').source := by
  ext z
  simp [immersionCompCoordChange, ModelWithCorners.toHomeomorph_symm_apply,
    J.range_eq_univ, Set.preimage_comp]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_target](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_target [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G) :
  (immersionCompCoordChange (J := J) e e').target = (J.extendCoordChange e e').target := by
  ext z
  simp [immersionCompCoordChange, ModelWithCorners.toHomeomorph_symm_apply,
    J.range_eq_univ, Set.preimage_comp]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompCoordChange_contDiffOn [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G)
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N) :
  ContDiffOn 𝕜 n (immersionCompCoordChange (J := J) e e')
    (immersionCompCoordChange (J := J) e e').source := by
  rw [immersionCompCoordChange_source]
  exact (J.contDiffOn_extendCoordChange he he').congr fun z _ ↦
    immersionCompCoordChange_apply e e' z

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_symm_apply [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G) (z : E'') :
  (immersionCompCoordChange (J := J) e e').symm z =
    (J.extendCoordChange e e').symm z := by
  simp [immersionCompCoordChange, ModelWithCorners.extendCoordChange, Function.comp_def]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_symm_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompCoordChange_symm_contDiffOn [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G)
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N) :
  ContDiffOn 𝕜 n (immersionCompCoordChange (J := J) e e').symm
    (immersionCompCoordChange (J := J) e e').target := by
  rw [immersionCompCoordChange_target]
  exact (J.contDiffOn_extendCoordChange_symm he he').congr fun z _ ↦
    immersionCompCoordChange_symm_apply e e' z

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_source](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_source {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
  (immersionCompTargetChange (J := J) e₂ e e').source =
    e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').target ×ˢ Set.univ) := by
  simp [immersionCompTargetChange]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_target](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_target {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) :
  (immersionCompTargetChange (J := J) e₂ e e').target =
    e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').source ×ˢ Set.univ) := by
  simp [immersionCompTargetChange]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_apply {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : E''') :
  immersionCompTargetChange (J := J) e₂ e e' z =
    e₂ ((immersionCompCoordChange (J := J) e e').symm (e₂.symm z).1, (e₂.symm z).2) := by
  simp [immersionCompTargetChange]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompTargetChange_symm_apply {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : E''') :
  (immersionCompTargetChange (J := J) e₂ e e').symm z =
    e₂ (immersionCompCoordChange (J := J) e e' (e₂.symm z).1, (e₂.symm z).2) := by
  simp [immersionCompTargetChange]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompTargetChange_contDiffOn {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N) :
  ContDiffOn 𝕜 n (immersionCompTargetChange (J := J) e₂ e e')
    (immersionCompTargetChange (J := J) e₂ e e').source := by
  rw [immersionCompTargetChange_source]
  have hprod := (immersionCompCoordChange_symm_contDiffOn e e' he he').prodMap
    (by fun_prop : ContDiffOn 𝕜 n (id : F → F) Set.univ)
  have hin := hprod.comp (by fun_prop : ContDiffOn 𝕜 n e₂.symm
    (e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').target ×ˢ Set.univ)))
    (fun _ hz ↦ hz)
  have hout := (by fun_prop : ContDiff 𝕜 n e₂).comp_contDiffOn hin
  exact hout.congr fun z _ ↦ by
    simpa [Function.comp_def, Prod.map] using immersionCompTargetChange_apply e₂ e e' z

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompTargetChange_symm_contDiffOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompTargetChange_symm_contDiffOn {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N) :
  ContDiffOn 𝕜 n (immersionCompTargetChange (J := J) e₂ e e').symm
    (immersionCompTargetChange (J := J) e₂ e e').target := by
  rw [immersionCompTargetChange_target]
  have hprod := (immersionCompCoordChange_contDiffOn e e' he he').prodMap
    (by fun_prop : ContDiffOn 𝕜 n (id : F → F) Set.univ)
  have hin := hprod.comp (by fun_prop : ContDiffOn 𝕜 n e₂.symm
    (e₂.symm ⁻¹' ((immersionCompCoordChange (J := J) e e').source ×ˢ Set.univ)))
    (fun _ hz ↦ hz)
  have hout := (by fun_prop : ContDiff 𝕜 n e₂).comp_contDiffOn hin
  exact hout.congr fun z _ ↦ by
    simpa [Function.comp_def, Prod.map] using immersionCompTargetChange_symm_apply e₂ e e' z

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompModelTargetChange_mem_contDiffGroupoid](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompModelTargetChange_mem_contDiffGroupoid {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N) :
  immersionCompModelTargetChange (J := J) (J' := J') e₂ e e' ∈ contDiffGroupoid n J' := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  constructor
  · change ContDiffOn 𝕜 n _ _
    convert immersionCompTargetChange_contDiffOn e₂ e e' he he' using 1 <;>
      ext z <;> simp [immersionCompModelTargetChange, Function.comp_def,
        ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]
  · change ContDiffOn 𝕜 n _ _
    convert immersionCompTargetChange_symm_contDiffOn e₂ e e' he he' using 1 <;>
      ext z <;> simp [immersionCompModelTargetChange, Function.comp_def,
        ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionComp_trans_mem_maximalAtlas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionComp_trans_mem_maximalAtlas
  {e : OpenPartialHomeomorph N' G'} {p : OpenPartialHomeomorph G' G'}
  (he : e ∈ IsManifold.maximalAtlas J' n N') (hp : p ∈ contDiffGroupoid n J') :
  e.trans p ∈ IsManifold.maximalAtlas J' n N' := by
  rw [IsManifold.mem_maximalAtlas_iff] at he ⊢
  intro e' he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n J').trans ((contDiffGroupoid n J').symm hp) (he e' he').1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid n J').trans (he e' he').2 hp

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCodChart_mem_maximalAtlas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionCompCodChart_mem_maximalAtlas {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
  (codChart : OpenPartialHomeomorph N' G')
  (he : e ∈ IsManifold.maximalAtlas J n N)
  (he' : e' ∈ IsManifold.maximalAtlas J n N)
  (hcod : codChart ∈ IsManifold.maximalAtlas J' n N') :
  immersionCompCodChart (J := J) (J' := J') e₂ e e' codChart ∈
    IsManifold.maximalAtlas J' n N' :=
  immersionComp_trans_mem_maximalAtlas hcod <|
    immersionCompModelTargetChange_mem_contDiffGroupoid e₂ e e' he he'

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCodChart_extend_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] [ChartedSpace G' N'] in
private lemma immersionCompCodChart_extend_apply {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G)
  (codChart : OpenPartialHomeomorph N' G') (z : N') :
  (immersionCompCodChart (J := J) (J' := J') e₂ e e' codChart).extend J' z =
    immersionCompTargetChange (J := J) e₂ e e' (codChart.extend J' z) := by
  simp [immersionCompCodChart, immersionCompModelTargetChange, Function.comp_def,
    ModelWithCorners.toHomeomorph_apply, J'.range_eq_univ]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompCoordChange_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompCoordChange_mem_source [J.Boundaryless]
  (e e' : OpenPartialHomeomorph N G) (hsource : e.source ⊆ e'.source)
  {z : E''} (hz : z ∈ (e.extend J).target) :
  z ∈ (immersionCompCoordChange (J := J) e e').source := by
  rw [immersionCompCoordChange_source, ← OpenPartialHomeomorph.extend_image_source_inter]
  rw [← PartialEquiv.image_source_eq_target] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hye : y ∈ e.source := by simpa using hy
  exact ⟨y, ⟨hye, hsource hye⟩, rfl⟩

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionComp_adapted_writtenInCharts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionComp_adapted_writtenInCharts {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  {g : N → N'} {y : N} (hg : IsImmersionAtOfComplement F J J' n g y)
  (e : OpenPartialHomeomorph N G) (hsource : e.source ⊆ hg.domChart.source) :
  Set.EqOn
    ((immersionCompCodChart (J := J) (J' := J') hg.equiv e hg.domChart hg.codChart).extend J' ∘
      g ∘ (e.extend J).symm)
    (hg.equiv ∘ (·, 0)) (e.extend J).target := by
  intro z hz
  have hzθ := immersionCompCoordChange_mem_source e hg.domChart hsource hz
  have hp : (e.extend J).symm z ∈ hg.domChart.source := by
    apply hsource
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend J).map_target hz
  have hθ : immersionCompCoordChange (J := J) e hg.domChart z =
    hg.domChart.extend J ((e.extend J).symm z) := by
    rw [immersionCompCoordChange_apply]
    rfl
  have hθtarget : immersionCompCoordChange (J := J) e hg.domChart z ∈
    (hg.domChart.extend J).target := by
    rw [hθ]
    exact (hg.domChart.extend J).map_source (by simpa using hp)
  have hback : (hg.domChart.extend J).symm
    (immersionCompCoordChange (J := J) e hg.domChart z) = (e.extend J).symm z := by
    rw [hθ, (hg.domChart.extend J).left_inv (by simpa using hp)]
  have hnormal : hg.codChart.extend J'
    (g ((hg.domChart.extend J).symm
      (immersionCompCoordChange (J := J) e hg.domChart z))) =
    hg.equiv (immersionCompCoordChange (J := J) e hg.domChart z, 0) := by
    simpa [Function.comp_def] using hg.writtenInCharts hθtarget
  simp only [Function.comp_apply]
  rw [immersionCompCodChart_extend_apply, ← hback, hnormal, immersionCompTargetChange_apply]
  simp [hzθ]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionCompModelTargetChange_mem_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
omit [ChartedSpace G N] in
private lemma immersionCompModelTargetChange_mem_source_iff {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  (e₂ : (E'' × F) ≃L[𝕜] E''') (e e' : OpenPartialHomeomorph N G) (z : G') :
  z ∈ (immersionCompModelTargetChange (J := J) (J' := J') e₂ e e').source ↔
    J' z ∈ (immersionCompTargetChange (J := J) e₂ e e').source := by
  simp [immersionCompModelTargetChange, ModelWithCorners.toHomeomorph_apply]

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[immersionComp_mem_codChart_source](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionComp_mem_codChart_source {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [J.Boundaryless] [J'.Boundaryless]
  {g : N → N'} {y : N} (hg : IsImmersionAtOfComplement F J J' n g y)
  (e : OpenPartialHomeomorph N G) (hy : y ∈ e.source)
  (hsource : e.source ⊆ hg.domChart.source) :
  g y ∈ (immersionCompCodChart (J := J) (J' := J') hg.equiv e hg.domChart
    hg.codChart).source := by
  rw [immersionCompCodChart, OpenPartialHomeomorph.trans_source]
  refine ⟨hg.mem_codChart_source, ?_⟩
  change hg.codChart (g y) ∈
    (immersionCompModelTargetChange (J := J) (J' := J') hg.equiv e hg.domChart).source
  rw [immersionCompModelTargetChange_mem_source_iff]
  have hy' : y ∈ hg.domChart.source := hsource hy
  have hz : e.extend J y ∈ (e.extend J).target :=
    (e.extend J).map_source (by simpa using hy)
  have hzθ := immersionCompCoordChange_mem_source e hg.domChart hsource hz
  have heback : (e.extend J).symm (e.extend J y) = y :=
    (e.extend J).left_inv (by simpa using hy)
  have hθ : immersionCompCoordChange (J := J) e hg.domChart (e.extend J y) =
    hg.domChart.extend J y := by
    rw [immersionCompCoordChange_apply]
    change hg.domChart.extend J ((e.extend J).symm (e.extend J y)) = _
    rw [heback]
  have hθtarget := (immersionCompCoordChange (J := J) e hg.domChart).map_source hzθ
  have hnormal : hg.codChart.extend J' (g y) = hg.equiv (hg.domChart.extend J y, 0) := by
    have h := hg.writtenInCharts ((hg.domChart.extend J).map_source (by simpa using hy'))
    have hgback : (hg.domChart.extend J).symm (hg.domChart.extend J y) = y :=
      (hg.domChart.extend J).left_inv (by simpa using hy')
    simp only [Function.comp_apply] at h
    rwa [hgback] at h
  change J' (hg.codChart (g y)) ∈ _
  change hg.codChart.extend J' (g y) ∈ _
  rw [hnormal, immersionCompTargetChange_source]
  simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply, Set.mem_prod,
    Set.mem_univ, and_true]
  rwa [← hθ]
set_option maxHeartbeats 800000 in

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
intermediate and target models are boundaryless, with the product of the two complements. -/
lemma _root_.Manifold.IsImmersionAtOfComplement.comp {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [J.Boundaryless] [J'.Boundaryless]
  {f : M → N} {g : N → N'} {x : M}
  (hg : IsImmersionAtOfComplement F₂ J J' n g (f x))
  (hf : IsImmersionAtOfComplement F₁ I J n f x) :
  IsImmersionAtOfComplement (F₁ × F₂) I J' n (g ∘ f) x := by
  obtain ⟨s, hs, hsopen, hxs⟩ := mem_nhds_iff.mp <|
    hf.continuousAt (hg.domChart.open_source.mem_nhds hg.mem_domChart_source)
  let domChart := hf.domChart.restr s
  let midChart := hf.codChart.restr hg.domChart.source
  let codChart := immersionCompCodChart (J := J) (J' := J') hg.equiv midChart
    hg.domChart hg.codChart
  have hdom_source : domChart.source = hf.domChart.source ∩ s :=
    hf.domChart.restr_source' s hsopen
  have hmid_source_eq : midChart.source = hf.codChart.source ∩ hg.domChart.source :=
    hf.codChart.restr_source' hg.domChart.source hg.domChart.open_source
  have hmid_source : midChart.source ⊆ hg.domChart.source := by
    rwa [hmid_source_eq]
  have hxdom : x ∈ domChart.source := by
    rw [hdom_source]
    exact ⟨hf.mem_domChart_source, hxs⟩
  have hxmid : f x ∈ midChart.source := by
    rw [hmid_source_eq]
    exact ⟨hf.mem_codChart_source, hg.mem_domChart_source⟩
  have hmap : domChart.source ⊆ f ⁻¹' midChart.source := by
    intro z hz
    rw [hdom_source] at hz
    rw [hmid_source_eq]
    exact ⟨hf.source_subset_preimage_source hz.1, hs hz.2⟩
  have hdom_mem : domChart ∈ IsManifold.maximalAtlas I n M := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hsopen
  have hmid_mem : midChart ∈ IsManifold.maximalAtlas J n N := by
    exact restr_mem_maximalAtlas (contDiffGroupoid n J) hf.codChart_mem_maximalAtlas
      hg.domChart.open_source
  have hcod_mem : codChart ∈ IsManifold.maximalAtlas J' n N' :=
    immersionCompCodChart_mem_maximalAtlas hg.equiv midChart hg.domChart hg.codChart
      hmid_mem hg.domChart_mem_maximalAtlas hg.codChart_mem_maximalAtlas
  have hxcod : g (f x) ∈ codChart.source :=
    immersionComp_mem_codChart_source hg midChart hxmid hmid_source
  apply IsImmersionAtOfComplement.mk_of_continuousAt
    (hg.continuousAt.comp hf.continuousAt) (immersionCompEquiv hf.equiv hg.equiv)
    domChart codChart hxdom hxcod hdom_mem hcod_mem
  have hgWritten := immersionComp_adapted_writtenInCharts hg midChart hmid_source
  intro z hz
  let p := (domChart.extend I).symm z
  have hpdom : p ∈ domChart.source := by
    simpa [p] using (domChart.extend I).map_target hz
  have hp : p ∈ hf.domChart.source := by
    rwa [hdom_source] at hpdom
  have hfz : hf.domChart.extend I p = z := by
    have h := (domChart.extend I).right_inv hz
    change domChart.extend I p = z at h
    rw [← h]
    rfl
  have hz' : z ∈ (hf.domChart.extend I).target := by
    rw [← hfz]
    exact (hf.domChart.extend I).map_source (by simpa using hp)
  have hfp : hf.codChart.extend J (f p) = hf.equiv (z, 0) := by
    have h := hf.writtenInCharts hz'
    have hback : (hf.domChart.extend I).symm z = p := by
      rw [← hfz, (hf.domChart.extend I).left_inv (by simpa using hp)]
    simpa only [Function.comp_apply, hback] using h
  have hpmid : f p ∈ midChart.source := hmap hpdom
  have hw : midChart.extend J (f p) = hf.equiv (z, 0) := by
    rwa [show midChart.extend J (f p) = hf.codChart.extend J (f p) by rfl]
  have hwt : midChart.extend J (f p) ∈ (midChart.extend J).target :=
    (midChart.extend J).map_source (by simpa using hpmid)
  have hgp := hgWritten hwt
  have hback : (midChart.extend J).symm (midChart.extend J (f p)) = f p :=
    (midChart.extend J).left_inv (by simpa using hpmid)
  simp only [Function.comp_apply, hback] at hgp
  change codChart.extend J' (g (f p)) = immersionCompEquiv hf.equiv hg.equiv (z, 0)
  rw [hgp, hw]
  exact (immersionCompEquiv_apply_zero hf.equiv hg.equiv z).symm

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
intermediate and target models are boundaryless. -/
lemma _root_.Manifold.IsImmersionAt.comp [J.Boundaryless] [J'.Boundaryless]
  {f : M → N} {g : N → N'} {x : M}
  (hg : IsImmersionAt J J' n g (f x)) (hf : IsImmersionAt I J n f x) :
  IsImmersionAt I J' n (g ∘ f) x :=
  (hg.isImmersionAtOfComplement_complement.comp
    hf.isImmersionAtOfComplement_complement).isImmersionAt

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
and target models are boundaryless, with the product of the two complements. -/
lemma _root_.Manifold.IsImmersionOfComplement.comp {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [J.Boundaryless] [J'.Boundaryless]
  {f : M → N} {g : N → N'}
  (hg : IsImmersionOfComplement F₂ J J' n g)
  (hf : IsImmersionOfComplement F₁ I J n f) :
  IsImmersionOfComplement (F₁ × F₂) I J' n (g ∘ f) :=
  fun x ↦ (hg (f x)).comp (hf x)

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E'' E''' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}
variable {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
variable {n : ℕ∞ω}
/--
[comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
boundaryless. -/
lemma _root_.Manifold.IsImmersion.comp [J.Boundaryless] [J'.Boundaryless]
  {f : M → N} {g : N → N'}
  (hg : IsImmersion J J' n g) (hf : IsImmersion I J n f) :
  IsImmersion I J' n (g ∘ f) :=
  (hg.isImmersionOfComplement_complement.comp
    hf.isImmersionOfComplement_complement).isImmersion

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

/--
[immersionAt_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
lemma immersionAt_comp
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [CompleteSpace E]
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [CompleteSpace E''] [CompleteSpace E''']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hf : IsImmersionAt I J n f x)
  (hg : IsImmersionAt J J' n g (f x)) :
-- imply
  IsImmersionAt I J' n (g ∘ f) x :=
-- proof
hg.comp hf

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

namespace MathlibExt.Geometry.Manifold.ImmersionCompWanted

/--
[immersion_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
lemma immersion_comp
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [CompleteSpace E]
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [CompleteSpace E''] [CompleteSpace E''']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
  {f : M → N}
  {g : N → N'}
-- given
  (hf : IsImmersion I J n f)
  (hg : IsImmersion J J' n g) :
-- imply
  IsImmersion I J' n (g ∘ f) := by
-- proof
  exact hg.comp hf

end MathlibExt.Geometry.Manifold.ImmersionCompWanted

/--
[_root_.Manifold.IsImmersionAtOfComplement.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma Manifold_IsImmersionAtOfComplement_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hg : IsImmersionAtOfComplement F₂ J J' n g (f x))
  (hf : IsImmersionAtOfComplement F₁ I J n f x) :
-- imply
  IsImmersionAtOfComplement (F₁ × F₂) I J' n (g ∘ f) x := by
-- proof
  apply Manifold.IsImmersionAtOfComplement.comp hg hf

/--
[_root_.Manifold.IsImmersionAt.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma Manifold_IsImmersionAt_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hg : IsImmersionAt J J' n g (f x))
  (hf : IsImmersionAt I J n f x) :
-- imply
  IsImmersionAt I J' n (g ∘ f) x := by
-- proof
  apply Manifold.IsImmersionAt.comp hg hf

/--
[_root_.Manifold.IsImmersionOfComplement.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma Manifold_IsImmersionOfComplement_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
-- given
  (hg : IsImmersionOfComplement F₂ J J' n g)
  (hf : IsImmersionOfComplement F₁ I J n f) :
-- imply
  IsImmersionOfComplement (F₁ × F₂) I J' n (g ∘ f) := by
-- proof
  apply Manifold.IsImmersionOfComplement.comp hg hf

/--
[_root_.Manifold.IsImmersion.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma Manifold_IsImmersion_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E'' E''' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
-- given
  (hg : IsImmersion J J' n g)
  (hf : IsImmersion I J n f) :
-- imply
  IsImmersion I J' n (g ∘ f) := by
-- proof
  apply Manifold.IsImmersion.comp hg hf


-- created on 2026-10-20
-- updated on 2026-10-23

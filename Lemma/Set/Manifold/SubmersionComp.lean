import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.SubmersionComp
open scoped Topology ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.SubmersionCompWanted


/--
[_root_.Manifold.IsSubmersionAtOfComplement.exists_domChart_of_codChart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma Manifold_IsSubmersionAtOfComplement_exists_domChart_of_codChart_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {n : ℕ∞ω}
  {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : M → N}
  {x : M}
  {codChart : OpenPartialHomeomorph N G}
-- given
  (hf : IsSubmersionAtOfComplement F I J n f x)
  (hfx : f x ∈ codChart.source)
  (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N) :
-- imply
  ∃ domChart : OpenPartialHomeomorph M H,
    x ∈ domChart.source ∧
    domChart ∈ IsManifold.maximalAtlas I n M ∧
    domChart.source ⊆ f ⁻¹' codChart.source ∧
    Set.EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm)
    (Prod.fst ∘ hf.equiv) (domChart.extend I).target := by
-- proof
  apply Manifold.IsSubmersionAtOfComplement.exists_domChart_of_codChart hf codChart hfx hcodChart

/--
[_root_.Manifold.IsSubmersionAtOfComplement.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma Manifold_IsSubmersionAtOfComplement_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'}
  {n : ℕ∞ω}
  {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hg : IsSubmersionAtOfComplement F₂ J J' n g (f x))
  (hf : IsSubmersionAtOfComplement F₁ I J n f x) :
-- imply
  IsSubmersionAtOfComplement (F₂ × F₁) I J' n (g ∘ f) x := by
-- proof
  apply Manifold.IsSubmersionAtOfComplement.comp hg hf

/--
[_root_.Manifold.IsSubmersionAt.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma Manifold_IsSubmersionAt_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'}
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hg : IsSubmersionAt J J' n g (f x))
  (hf : IsSubmersionAt I J n f x) :
-- imply
  IsSubmersionAt I J' n (g ∘ f) x := by
-- proof
  apply Manifold.IsSubmersionAt.comp hg hf

/--
[_root_.Manifold.IsSubmersionOfComplement.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma Manifold_IsSubmersionOfComplement_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'}
  {n : ℕ∞ω}
  {F₁ F₂ : Type u} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {f : M → N}
  {g : N → N'}
-- given
  (hg : IsSubmersionOfComplement F₂ J J' n g)
  (hf : IsSubmersionOfComplement F₁ I J n f) :
-- imply
  IsSubmersionOfComplement (F₂ × F₁) I J' n (g ∘ f) := by
-- proof
  apply Manifold.IsSubmersionOfComplement.comp hg hf

/--
[_root_.Manifold.IsSubmersion.comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma Manifold_IsSubmersion_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'}
  {n : ℕ∞ω}
  {f : M → N}
  {g : N → N'}
-- given
  (hg : IsSubmersion J J' n g)
  (hf : IsSubmersion I J n f) :
-- imply
  IsSubmersion I J' n (g ∘ f) := by
-- proof
  apply Manifold.IsSubmersion.comp hg hf

/--
[submersionAt_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma submersionAt_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [CompleteSpace E''']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [CompleteSpace E] [CompleteSpace E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
  {f : M → N}
  {g : N → N'}
  {x : M}
-- given
  (hf : IsSubmersionAt I J n f x)
  (hg : IsSubmersionAt J J' n g (f x)) :
-- imply
  IsSubmersionAt I J' n (g ∘ f) x := by
-- proof
  apply MathlibExt.Geometry.Manifold.SubmersionCompWanted.submersionAt_comp hf hg

/--
[submersion_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionComp.lean)
-/
@[path]
private lemma submersion_comp_eq
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E'''] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N'] [CompleteSpace E''']
  {E E'' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [CompleteSpace E] [CompleteSpace E'']
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {J : ModelWithCorners 𝕜 E'' G} [J.Boundaryless]
  {J' : ModelWithCorners 𝕜 E''' G'} [J'.Boundaryless]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] [IsManifold J' n N']
  {f : M → N}
  {g : N → N'}
-- given
  (hf : IsSubmersion I J n f)
  (hg : IsSubmersion J J' n g) :
-- imply
  IsSubmersion I J' n (g ∘ f) := by
-- proof
  apply MathlibExt.Geometry.Manifold.SubmersionCompWanted.submersion_comp hf hg


-- created on 2026-10-20

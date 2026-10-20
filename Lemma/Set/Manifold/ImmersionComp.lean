import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.ImmersionComp
open scoped Topology ContDiff
open Manifold
open MathlibExt.Geometry.Manifold.ImmersionCompWanted


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

/--
[immersionAt_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersionAt_comp_eq
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
  IsImmersionAt I J' n (g ∘ f) x := by
-- proof
  apply MathlibExt.Geometry.Manifold.ImmersionCompWanted.immersionAt_comp hf hg

/--
[immersion_comp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionComp.lean)
-/
@[path]
private lemma immersion_comp_eq
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
  apply MathlibExt.Geometry.Manifold.ImmersionCompWanted.immersion_comp hf hg


-- created on 2026-10-20

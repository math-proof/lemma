import Mathlib
import sympy.Basic
import Structure.v1.Atlas.LieGroups.code.InfinitesimalEquivalenceCore.Part3

/--
[Globalization.ι_denseRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/InfinitesimalEquivalenceCore.lean)
-/
@[path]
private lemma Globalization.ι_denseRange
  [Group G]
  [TopologicalSpace G]
  [Group K]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {K_sub : K →* G} [CompactSpace K_sub.range]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {G_glob : Globalization G K_sub M} :
-- imply
  @DenseRange G_glob.Ŵ G_glob.instNACG.toUniformSpace.toTopologicalSpace V G_glob.ι := by
-- proof
  let _ := G_glob.instNACG
  let _ := G_glob.instIPS
  let _ := G_glob.instCS
  have hdense : Dense (ContinuousRep.kFiniteSubspace G_glob.π K_sub.range : Set G_glob.Ŵ) :=
    ContinuousRep.kFiniteSubspace_dense G_glob.π K_sub.range
  rwa [DenseRange, G_glob.kfin_image]

-- created on 2026-10-23
-- updated on 2026-10-24

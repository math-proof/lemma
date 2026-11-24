module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.v1.Atlas.LieGroups.code.Globalization
open scoped Cardinal


public section

/--
[gkmodule_has_countable_spanning_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Globalization.lean)
-/
@[reducible] def Globalization.topologicalSpaceŴ
  {G : Type*} [Group G] [TopologicalSpace G]
  {K : Type*} [Group K] {K_sub : K →* G}
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  (Gl : Globalization G K_sub M) : TopologicalSpace Gl.Ŵ :=
  Gl.instNACG.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
@[reducible] def Globalization.addCommGroupŴ
  {G : Type*} [Group G] [TopologicalSpace G]
  {K : Type*} [Group K] {K_sub : K →* G}
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  (Gl : Globalization G K_sub M) : AddCommGroup Gl.Ŵ :=
  Gl.instNACG.toAddCommGroup
@[reducible] def Globalization.moduleŴ
  {G : Type*} [Group G] [TopologicalSpace G]
  {K : Type*} [Group K] {K_sub : K →* G}
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  (Gl : Globalization G K_sub M) :
  @Module ℂ Gl.Ŵ _ Gl.addCommGroupŴ.toAddCommMonoid :=
  Gl.instIPS.toNormedSpace.toModule

/--
[adjoin_range_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Globalization.lean)
-/

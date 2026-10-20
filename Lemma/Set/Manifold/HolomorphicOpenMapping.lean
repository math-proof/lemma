import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.HolomorphicOpenMapping
open Set Manifold
open scoped Manifold
open Topology Filter
open MDifferentiable
open MathlibExt.Geometry.Manifold.ComplexRigidityWanted


/--
[isOpenMap_of_finrank_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicOpenMapping.lean)
-/
@[path]
private lemma isOpenMap_of_finrank_eq_one_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {J : ModelWithCorners ℂ F G} [J.Boundaryless] [IsManifold J 1 N]
  {f : M → N}
-- given
  (hE : Module.finrank ℂ E = 1)
  (hF : Module.finrank ℂ F = 1)
  (hf : MDiff f)
  (hf_nonconst : ∃ x y : M, f x ≠ f y) :
-- imply
  IsOpenMap f := by
-- proof
  apply MDifferentiable.isOpenMap_of_finrank_eq_one hE hF hf hf_nonconst

/--
[holomorphic_open_mapping_one_dim](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicOpenMapping.lean)
-/
@[path]
private lemma holomorphic_open_mapping_one_dim_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {J : ModelWithCorners ℂ F G} [J.Boundaryless] [IsManifold J 1 N]
  {f : M → N}
-- given
  (hE : Module.finrank ℂ E = 1)
  (hF : Module.finrank ℂ F = 1)
  (hf : MDiff f)
  (hf_nonconst : ∃ x y : M, f x ≠ f y) :
-- imply
  IsOpenMap f := by
-- proof
  apply MathlibExt.Geometry.Manifold.ComplexRigidityWanted.holomorphic_open_mapping_one_dim hE hF hf hf_nonconst


-- created on 2026-10-20

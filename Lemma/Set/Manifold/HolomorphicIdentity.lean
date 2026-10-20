import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Manifold.HolomorphicIdentity
open Set Manifold
open scoped Manifold
open MDifferentiable
open MathlibExt.Geometry.Manifold.ComplexRigidityWanted


/--
[eq_of_eqOn_of_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicIdentity.lean)
-/
@[path]
private lemma eq_of_eqOn_of_isOpen_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f g : M → F}
  {U : Set M}
-- given
  (hf : MDiff f)
  (hg : MDiff g)
  (hU_open : IsOpen U)
  (hU_nonempty : U.Nonempty)
  (h_eq : EqOn f g U) :
-- imply
  f = g := by
-- proof
  apply MDifferentiable.eq_of_eqOn_of_isOpen hf hg hU_open hU_nonempty h_eq

/--
[holomorphic_identity_on_connected_complex_manifold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicIdentity.lean)
-/
@[path]
private lemma holomorphic_identity_on_connected_complex_manifold_eq
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [ConnectedSpace M]
  {I : ModelWithCorners ℂ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f g : M → F}
  {U : Set M}
-- given
  (hf : MDiff f)
  (hg : MDiff g)
  (hU_open : IsOpen U)
  (hU_nonempty : U.Nonempty)
  (h_eq : EqOn f g U) :
-- imply
  f = g := by
-- proof
  apply MathlibExt.Geometry.Manifold.ComplexRigidityWanted.holomorphic_identity_on_connected_complex_manifold hf hg hU_open hU_nonempty h_eq


-- created on 2026-10-20

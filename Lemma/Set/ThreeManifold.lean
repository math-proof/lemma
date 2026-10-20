import Mathlib
import sympy.Basic
import sympy.atlas.Topology.ThreeManifold


/--
[isThreeManifold_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean)
-/
@[path]
private lemma isThreeManifold_iff_eq
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
-- imply
  IsThreeManifold M ↔ T2Space M ∧ SecondCountableTopology M := by
-- proof
  apply isThreeManifold_iff M

/--
[IsThreeManifold.locallyCompactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean)
-/
@[path]
private lemma IsThreeManifold_locallyCompactSpace_eq
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsThreeManifold M] :
-- imply
  LocallyCompactSpace M := by
-- proof
  apply IsThreeManifold.locallyCompactSpace M


-- created on 2026-10-20

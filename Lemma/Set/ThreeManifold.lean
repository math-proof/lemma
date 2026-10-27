import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.ThreeManifold


/--
[isThreeManifold_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean)
-/
@[path]
lemma isThreeManifold_iff
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
-- imply
  IsThreeManifold M ↔ T2Space M ∧ SecondCountableTopology M :=
-- proof
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨⟩⟩

/--
[IsThreeManifold.locallyCompactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/ThreeManifold.lean)
-/
@[path]
lemma IsThreeManifold.locallyCompactSpace
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsThreeManifold M] :
-- imply
  LocallyCompactSpace M :=
-- proof
  ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M


-- created on 2026-10-20
-- updated on 2026-10-26

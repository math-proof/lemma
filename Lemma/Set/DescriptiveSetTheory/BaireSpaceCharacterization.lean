import Mathlib
import sympy.Basic
import sympy.atlas.Topology.DescriptiveSetTheory.BaireSpaceCharacterization
open Set Topology
open Filter Metric EMetric
open MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted


/--
[baire_space_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/BaireSpaceCharacterization.lean)
-/
@[path]
private lemma baire_space_characterization_eq
  [TopologicalSpace X] [PolishSpace X] [Nonempty X]
-- given
  (hZero : IsZeroDimensionalSpace X)
  (hCompact : ∀ (K : Set X), IsCompact K → interior K = ∅) :
-- imply
  Nonempty (X ≃ₜ (ℕ → ℕ)) := by
-- proof
  apply MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted.baire_space_characterization hZero hCompact


-- created on 2026-10-20

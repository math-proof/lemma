import Mathlib
import sympy.Basic
import sympy.atlas.Topology.DescriptiveSetTheory.CantorSpaceCharacterization
open MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted


/--
[brouwer_cantor_space_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/CantorSpaceCharacterization.lean)
-/
@[path]
private lemma brouwer_cantor_space_characterization_eq
  [TopologicalSpace X] [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [PerfectSpace X] [TotallyDisconnectedSpace X] [Nonempty X] :
-- imply
  Nonempty (X ≃ₜ (ℕ → Bool)) := by
-- proof
  apply MathlibExt.Topology.DescriptiveSetTheory.CantorSpaceCharacterizationWanted.brouwer_cantor_space_characterization


-- created on 2026-10-20

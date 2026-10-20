import Mathlib
import sympy.Basic
import sympy.atlas.Topology.DescriptiveSetTheory.RationalsCharacterization
open Set Filter
open MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted


/--
[sierpinski_rationals_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/RationalsCharacterization.lean)
-/
@[path]
private lemma sierpinski_rationals_characterization_eq
  [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [PerfectSpace X] [Countable X] [Nonempty X] :
-- imply
  Nonempty (X ≃ₜ ℚ) := by
-- proof
  apply MathlibExt.Topology.DescriptiveSetTheory.RationalsCharacterizationWanted.sierpinski_rationals_characterization


-- created on 2026-10-20

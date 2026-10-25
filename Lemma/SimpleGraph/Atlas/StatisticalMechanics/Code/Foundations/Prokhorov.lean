import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
open MeasureTheory TopologicalSpace Filter Topology StatMech


/--
[prokhorov_compactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Prokhorov.lean)
-/
@[path]
private lemma prokhorov_compactSpace_eq
  [Countable E] :
-- imply
  CompactSpace (ProbabilityMeasure (ConfigSpace E)) := by
-- proof
  apply StatMech.prokhorov_compactSpace

/--
[prokhorov_metrizableSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Prokhorov.lean)
-/
@[path]
private lemma prokhorov_metrizableSpace_eq
  [Countable E] :
-- imply
  MetrizableSpace (ProbabilityMeasure (ConfigSpace E)) := by
-- proof
  apply StatMech.prokhorov_metrizableSpace

/--
[prokhorov_secondCountableTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Prokhorov.lean)
-/
@[path]
private lemma prokhorov_secondCountableTopology_eq
  [Countable E] :
-- imply
  SecondCountableTopology (ProbabilityMeasure (ConfigSpace E)) := by
-- proof
  apply StatMech.prokhorov_secondCountableTopology

/--
[prokhorov_seq_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Prokhorov.lean)
-/
@[path]
private lemma prokhorov_seq_compact_eq
  [Countable E]
  {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} :
-- imply
  ∃ (ν : ProbabilityMeasure (ConfigSpace E)) (φ : ℕ → ℕ), StrictMono φ ∧ WeakConvergesTo (μ ∘ φ) ν := by
-- proof
  apply StatMech.prokhorov_seq_compact μ


-- created on 2026-10-23

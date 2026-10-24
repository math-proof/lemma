/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/BaireSpaceCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.CantorScheme

section
/-!
# Baire space characterization
-/

noncomputable section

open Set Topology

namespace MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted

open Filter Metric EMetric

/-- Zero-dimensional via clopen neighborhoods. -/
def IsZeroDimensionalSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U
end MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted

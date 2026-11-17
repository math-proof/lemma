/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/DescriptiveSetTheory/BaireSpaceCharacterization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.MetricSpace.CantorScheme

@[expose] public section

/-!
# Baire space characterization
-/


section

noncomputable section

open Set Topology

namespace MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted

open Filter Metric EMetric

/-- Zero-dimensional via clopen neighborhoods. -/
def IsZeroDimensionalSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U

end MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted
end
end

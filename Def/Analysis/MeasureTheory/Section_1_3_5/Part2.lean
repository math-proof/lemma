import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
import Mathlib.Topology.UrysohnsLemma
import Theorem.Analysis.MeasureTheory.Section_1_3_5.Part2


def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0


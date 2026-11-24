module
public import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part7
public import Mathlib.Topology.UrysohnsLemma
public import Theorem.Analysis.MeasureTheory.Section_1_3_5.Part2


public section

def CompactlySupported {X Y:Type*} [TopologicalSpace X] [Zero Y] (f: X → Y) : Prop :=
  ∃ (K: Set X), IsCompact K ∧ ∀ x, x ∉ K → f x = 0


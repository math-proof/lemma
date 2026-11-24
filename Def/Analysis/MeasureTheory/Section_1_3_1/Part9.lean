module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part8


public section

/-- Definition 1.3.5 (almost always) -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 (almost everywhere equal) -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 (support) -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }


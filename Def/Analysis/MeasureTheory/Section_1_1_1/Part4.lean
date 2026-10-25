import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part12
open BoundedInterval


/-- The bounded interval with the given endpoints, open or closed at each end as specified. -/
def BoundedInterval.mk' (a b : ℝ) (lclosed uclosed : Bool) : BoundedInterval :=
  match lclosed, uclosed with
  | true, true => Icc a b
  | true, false => Ico a b
  | false, true => Ioc a b
  | false, false => Ioo a b

/-- Whether a bounded interval contains its left endpoint. -/
def BoundedInterval.lclosed : BoundedInterval → Bool
  | Icc _ _ => true
  | Ico _ _ => true
  | Ioo _ _ => false
  | Ioc _ _ => false

/-- Whether a bounded interval contains its right endpoint. -/
def BoundedInterval.uclosed : BoundedInterval → Bool
  | Icc _ _ => true
  | Ioc _ _ => true
  | Ioo _ _ => false
  | Ico _ _ => false


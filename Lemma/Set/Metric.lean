import Mathlib
import sympy.Basic
import Def.Geometry.Metric.Part2
open scoped Finset


/--
[unitDistNum_le_choose_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean)
-/
@[path]
lemma unitDistNum_le_choose_two
  [MetricSpace X]
  {X}
  {s : Finset X} :
-- imply
  unitDistNum s ≤ (#s).choose 2 := by
-- proof
  unfold unitDistNum distanceMultiplicity
  calc #(s.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = 1) / 2
    ≤ #s.offDiag / 2 := Nat.div_le_div_right (Finset.card_filter_le _ _)
    _ = (#s).choose 2 := by
      rw [Finset.offDiag_card, Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one]

/--
[unitDistNum_eq_distanceMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean)
-/
@[path]
private lemma unitDistNum_eq_distanceMultiplicity_eq
  [MetricSpace X]
  {s : Finset X} :
-- imply
  unitDistNum s = distanceMultiplicity s 1 := by
-- proof
  apply unitDistNum_eq_distanceMultiplicity s


-- created on 2026-10-20
-- updated on 2026-10-23

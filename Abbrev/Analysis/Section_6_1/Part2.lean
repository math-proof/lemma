import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Instance.Analysis.Section_6_1


namespace Chapter6

@[coe]
abbrev Sequence.ofNatFun (a:ℕ → ℝ) : Sequence :=
 {
    m := 0
    seq n := if n ≥ 0 then a n.toNat else 0
    vanish := by simp_all
 }

end Chapter6

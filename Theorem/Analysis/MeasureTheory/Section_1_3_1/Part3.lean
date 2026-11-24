module
public import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
public import Theorem.Analysis.Misc.NatBitwise
public import Def.Analysis.MeasureTheory.Section_1_3_1.Part3


public section

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

lemma atomMembership_eq_testBit (k k' n i : ℕ) : atomMembership k k' n i = n.testBit i := by
  simp only [atomMembership, Nat.testBit_eq_decide_div_mod_eq]

end UnsignedSimpleFunction.IntegralWellDef

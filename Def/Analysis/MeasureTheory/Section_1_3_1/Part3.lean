import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part2


noncomputable def UnsignedSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-! ## Helper lemmas for Lemma 1.3.4

The proof uses a Venn diagram argument: given two representations of the same simple function,
we partition R^d into atoms (intersections of all sets and their complements), express each
original set as a disjoint union of atoms, and use finite additivity of Lebesgue measure.
-/

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- {given -show}`k, k'` Given families of sets indexed by {lean}`Fin k` and {lean}`Fin k'`, an atom is determined by
    a choice of “in” or “out” for each set. We encode this as a {lean}`Fin (2^(k+k'))` index. -/
def atomMembership (_k _k' : ℕ) (n : ℕ) (i : ℕ) : Bool := (n / 2^i) % 2 = 1

end UnsignedSimpleFunction.IntegralWellDef

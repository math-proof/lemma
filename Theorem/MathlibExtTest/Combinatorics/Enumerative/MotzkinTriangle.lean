/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MotzkinTriangle.lean -/


import Def.Combinatorics.Enumerative.MotzkinTriangle.Part5
import Lemma.Finset.Enumerative.MotzkinTriangle
import Mathlib.Tactic


namespace MetaMathlibExt

example : PowerSeries.coeff 0 motzkinDiscriminant = 1 := by
  norm_num [motzkinDiscriminant]

example : PowerSeries.coeff 1 motzkinDiscriminant = -2 := by
  norm_num [motzkinDiscriminant, PowerSeries.coeff_one_mul,
    PowerSeries.coeff_X_pow]

example (p : MotzkinRiordanPair) : IsMotzkinRiordanPair p.g p.h :=
  p.isPair

example (p : MotzkinRiordanPair) (n : ℕ) : p.entry n 0 = p.g.coeff n := by
  simp

example : IsMotzkinRiordanPair motzkinRiordanPair.g motzkinRiordanPair.h :=
  motzkinRiordanPair.isPair

/-- The first four rows of the canonical triangle agree with OEIS A094531. -/
example :
    [[motzkinTriangle 0 0],
      [motzkinTriangle 1 0, motzkinTriangle 1 1],
      [motzkinTriangle 2 0, motzkinTriangle 2 1, motzkinTriangle 2 2],
      [motzkinTriangle 3 0, motzkinTriangle 3 1,
        motzkinTriangle 3 2, motzkinTriangle 3 3]] =
    [[1], [1, 1], [3, 2, 1], [7, 6, 3, 1]] := by
  exact motzkinTriangle_initial_rows

#print axioms motzkinDiscriminant
#print axioms IsMotzkinSquareRoot
#print axioms IsMotzkinRiordanPair
#print axioms MotzkinRiordanPair.entry
#print axioms motzkinRiordanPair
#print axioms motzkinTriangle

end MetaMathlibExt

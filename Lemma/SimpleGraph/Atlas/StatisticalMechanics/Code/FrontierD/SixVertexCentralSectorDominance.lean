import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexHalfFilledSectorTop_ge_two_add_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexHalfFilledSectorTop_ge_two_add_pow_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n = N)
  (hc : 0 < c) :
-- imply
  2 + c ^ N <= sixVertexSectorTopEigenvalue N n (by omega) c := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledSectorTop_ge_two_add_pow hn hhalf hc

/--
[sixVertexSectorTopEigenvalue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_zero_eq
  {N : Nat}
  {c : Real}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexSectorTopEigenvalue N 0 (Nat.zero_le N) c = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_zero N hc

/--
[sixVertexSectorTopEigenvalue_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_full_eq
  {N : Nat}
  {c : Real}
-- given
  (hc : 0 < c) :
-- imply
  sixVertexSectorTopEigenvalue N N (le_refl N) c = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_full N hc

/--
[sixVertexSectorTopEigenvalue_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_one_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : 0 < N)
  (hc : 0 < c) :
-- imply
  sixVertexSectorTopEigenvalue N 1 (by omega) c = 2 + (N - 1 : Nat) * c ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_one hN hc

/--
[natCast_succ_le_real_pow_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma natCast_succ_le_real_pow_of_two_le_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 <= c) :
-- imply
  ((k + 1 : Nat) : Real) <= c ^ k := by
-- proof
  apply StatMech.FrontierD.natCast_succ_le_real_pow_of_two_le hc k

/--
[sixVertexSectorTopEigenvalue_one_le_halfFilled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_one_le_halfFilled_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : 4 <= N)
  (hhalf : 2 * (N / 2) = N)
  (hc : 0 < c)
  (hc2 : 2 <= c) :
-- imply
  sixVertexSectorTopEigenvalue N 1 (by omega) c <= sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_one_le_halfFilled hN hhalf hc hc2

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_iff_eq
  {N : Nat}
  {c : Real} :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c ↔ ∀ m : Fin (N + 1), sixVertexWidthSectorTopEigenvalue N c m <= sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_iff N c

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hdom : ∀ n : Nat, (hn : n <= N / 2) -> sixVertexSectorTopEigenvalue N n (hn.trans (Nat.div_le_self N 2)) c <= sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c) :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_of_lowerHalf N hN c hdom

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hNpos : 0 < N)
  (hc : 0 < c)
  (hdom : SixVertexStrictLowerHalfDominance N c) :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalf N hN hNpos hc hdom

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCentralSectorDominance.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hN4 : 4 <= N)
  (hc : 0 < c)
  (hc2 : 2 <= c)
  (hdom : SixVertexStrictLowerHalfDominanceAboveOne N c) :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_of_strictLowerHalfAboveOne N hN hN4 hc hc2 hdom


-- created on 2026-10-23

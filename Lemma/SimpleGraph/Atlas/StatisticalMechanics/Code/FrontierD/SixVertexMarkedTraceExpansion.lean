import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part7
open Finset Matrix StatMech StatMech.FrontierD


/--
[eval_sixVertexShiftedSectorTransferPolynomial_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma eval_sixVertexShiftedSectorTransferPolynomial_apply_eq
  {N n : Nat}
  {t : Real}
  {x y : SixVertexSector N n} :
-- imply
  eval t (sixVertexShiftedSectorTransferPolynomial N n x y) = sixVertexSectorTransfer N n (2 + t) x y := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexShiftedSectorTransferPolynomial_apply N n t x y

/--
[map_sixVertexShiftedSectorTransferPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma map_sixVertexShiftedSectorTransferPolynomial_eq
  {N n : Nat}
  {t : Real} :
-- imply
  (sixVertexShiftedSectorTransferPolynomial N n).map (evalRingHom t) = sixVertexSectorTransfer N n (2 + t) := by
-- proof
  apply StatMech.FrontierD.map_sixVertexShiftedSectorTransferPolynomial N n t

/--
[Polynomial.coeffNonnegative_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_zero_eq :
-- imply
  Polynomial.CoeffNonnegative (0 : Real[X]) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_zero

/--
[Polynomial.coeffNonnegative_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_one_eq :
-- imply
  Polynomial.CoeffNonnegative (1 : Real[X]) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_one

/--
[Polynomial.coeffNonnegative_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_add_eq
  {p q : Real[X]}
-- given
  (hp : Polynomial.CoeffNonnegative p)
  (hq : Polynomial.CoeffNonnegative q) :
-- imply
  Polynomial.CoeffNonnegative (p + q) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_add hp hq

/--
[Polynomial.coeffNonnegative_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_mul_eq
  {p q : Real[X]}
-- given
  (hp : Polynomial.CoeffNonnegative p)
  (hq : Polynomial.CoeffNonnegative q) :
-- imply
  Polynomial.CoeffNonnegative (p * q) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_mul hp hq

/--
[Polynomial.coeffNonnegative_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_pow_eq
  {p : Real[X]}
  {m : Nat}
-- given
  (hp : Polynomial.CoeffNonnegative p) :
-- imply
  Polynomial.CoeffNonnegative (p ^ m) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_pow hp m

/--
[Polynomial.coeffNonnegative_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_sum_eq
  {s : Finset alpha}
-- given
  (f : alpha -> Real[X])
  (hf : ∀ i ∈ s, Polynomial.CoeffNonnegative (f i)) :
-- imply
  Polynomial.CoeffNonnegative (∑ i ∈ s, f i) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_sum s f hf

/--
[Polynomial.coeffNonnegative_two_add_X](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeffNonnegative_two_add_X_eq :
-- imply
  Polynomial.CoeffNonnegative (C 2 + X : Real[X]) := by
-- proof
  apply StatMech.FrontierD.Polynomial.coeffNonnegative_two_add_X

/--
[sixVertexShiftedSectorTransferPolynomial_coeffNonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma sixVertexShiftedSectorTransferPolynomial_coeffNonnegative_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  Polynomial.CoeffNonnegative (sixVertexShiftedSectorTransferPolynomial N n x y) := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftedSectorTransferPolynomial_coeffNonnegative N n x y

/--
[sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative_eq
  {N n M : Nat}
  {x y : SixVertexSector N n} :
-- imply
  Polynomial.CoeffNonnegative ((sixVertexShiftedSectorTransferPolynomial N n ^ M) x y) := by
-- proof
  apply StatMech.FrontierD.sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative N n M x y

/--
[eval_sixVertexShiftedSectorTracePolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma eval_sixVertexShiftedSectorTracePolynomial_eq
  {N M n : Nat}
  {t : Real} :
-- imply
  eval t (sixVertexShiftedSectorTracePolynomial N M n) = Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexShiftedSectorTracePolynomial N M n t

/--
[sixVertexMarkedSectorTraceCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma sixVertexMarkedSectorTraceCoefficient_nonneg_eq
  {N M n k : Nat} :
-- imply
  0 <= sixVertexMarkedSectorTraceCoefficient N M n k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorTraceCoefficient_nonneg N M n k

/--
[coeff_sixVertexMarkedFugacityPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeff_sixVertexMarkedFugacityPolynomial_eq
  {N M k n : Nat}
-- given
  (hn : n <= N) :
-- imply
  (sixVertexMarkedFugacityPolynomial N M k).coeff n = sixVertexMarkedSectorTraceCoefficient N M n k := by
-- proof
  apply StatMech.FrontierD.coeff_sixVertexMarkedFugacityPolynomial N M k n hn

/--
[eval_sixVertexMarkedTraceLogConcavityDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma eval_sixVertexMarkedTraceLogConcavityDifference_eq
  {N M n : Nat}
  {t : Real} :
-- imply
  eval t (sixVertexMarkedTraceLogConcavityDifference N M n) = Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) ^ 2 - Matrix.trace (sixVertexSectorTransfer N (n - 1) (2 + t) ^ M) * Matrix.trace (sixVertexSectorTransfer N (n + 1) (2 + t) ^ M) := by
-- proof
  apply StatMech.FrontierD.eval_sixVertexMarkedTraceLogConcavityDifference N M n t

/--
[coeff_sixVertexMarkedTraceLogConcavityDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeff_sixVertexMarkedTraceLogConcavityDifference_eq
  {N M n k : Nat} :
-- imply
  (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k = ∑ ij ∈ Finset.antidiagonal k, (sixVertexMarkedSectorTraceCoefficient N M n ij.1 * sixVertexMarkedSectorTraceCoefficient N M n ij.2 - sixVertexMarkedSectorTraceCoefficient N M (n - 1) ij.1 * sixVertexMarkedSectorTraceCoefficient N M (n + 1) ij.2) := by
-- proof
  apply StatMech.FrontierD.coeff_sixVertexMarkedTraceLogConcavityDifference N M n k

/--
[coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range_eq
  {N M n k : Nat} :
-- imply
  (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k = ∑ i ∈ Finset.range (k + 1), (sixVertexMarkedSectorTraceCoefficient N M n i * sixVertexMarkedSectorTraceCoefficient N M n (k - i) - sixVertexMarkedSectorTraceCoefficient N M (n - 1) i * sixVertexMarkedSectorTraceCoefficient N M (n + 1) (k - i)) := by
-- proof
  apply StatMech.FrontierD.coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range N M n k

/--
[SixVertexMarkedAntidiagonalSuffixNonnegative.coefficientwiseLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma coefficientwiseLogConcave_eq
  {N M n : Nat}
-- given
  (h : SixVertexMarkedAntidiagonalSuffixNonnegative N M n) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave N M n := by
-- proof
  apply StatMech.FrontierD.SixVertexMarkedAntidiagonalSuffixNonnegative.coefficientwiseLogConcave h

/--
[Polynomial.eval_nonneg_of_coeff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma eval_nonneg_of_coeff_nonneg_eq
  {p : Real[X]}
  {t : Real}
-- given
  (ht : 0 <= t)
  (hcoeff : forall k, 0 <= p.coeff k) :
-- imply
  0 <= p.eval t := by
-- proof
  apply StatMech.FrontierD.Polynomial.eval_nonneg_of_coeff_nonneg p t ht hcoeff

/--
[sixVertexSectorTrace_logConcave_of_markedCoefficientwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_markedCoefficientwise_eq
  {N M n : Nat}
  {c : Real}
-- given
  (hc : 2 <= c)
  (hcoeff : SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
-- imply
  Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) * Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <= Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_markedCoefficientwise N M n hc hcoeff

/--
[sixVertexSectorTraceLogConcave_of_markedCoefficientwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean)
-/
@[path]
private lemma sixVertexSectorTraceLogConcave_of_markedCoefficientwise_eq
  {N : Nat}
  {c : Real}
-- given
  (hc : 2 <= c)
  (hcoeff : forall M n : Nat, 0 < M -> 0 < n -> n < N -> SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
-- imply
  SixVertexSectorTraceLogConcave N c := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTraceLogConcave_of_markedCoefficientwise N hc hcoeff


-- created on 2026-10-23

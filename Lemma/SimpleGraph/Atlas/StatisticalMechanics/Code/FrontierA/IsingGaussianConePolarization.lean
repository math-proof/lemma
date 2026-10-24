import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization
open Filter Finset Polynomial Topology StatMech StatMech.FrontierA


/--
[polynomial_eval_tendsto_zero_of_nodes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma polynomial_eval_tendsto_zero_of_nodes_eq
  {degree : Nat}
  {x : Real}
-- given
  (p : Nat -> Real[X])
  (hdegree : forall scale, (p scale).degree < (degree + 1 : Nat))
  (hnodes : forall i : Fin (degree + 1), Tendsto (fun scale => (p scale).eval ((i : Nat) : Real)) atTop (nhds 0)) :
-- imply
  Tendsto (fun scale => (p scale).eval x) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.polynomial_eval_tendsto_zero_of_nodes degree p hdegree hnodes x

/--
[smearingPositivePart_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearingPositivePart_nonneg_eq
  {v : V}
-- given
  (a : V -> Real) :
-- imply
  0 <= smearingPositivePart a v := by
-- proof
  apply StatMech.FrontierA.smearingPositivePart_nonneg a v

/--
[smearingNegativePart_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearingNegativePart_nonneg_eq
  {v : V}
-- given
  (a : V -> Real) :
-- imply
  0 <= smearingNegativePart a v := by
-- proof
  apply StatMech.FrontierA.smearingNegativePart_nonneg a v

/--
[smearing_eq_positivePart_sub_negativePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearing_eq_positivePart_sub_negativePart_eq
-- given
  (a : V -> Real) :
-- imply
  a = smearingPositivePart a - smearingNegativePart a := by
-- proof
  apply StatMech.FrontierA.smearing_eq_positivePart_sub_negativePart a

/--
[smearingStrictPositivePart_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearingStrictPositivePart_pos_eq
  [Fintype V]
  {v : V}
-- given
  (a : V -> Real) :
-- imply
  0 < smearingStrictPositivePart a v := by
-- proof
  apply StatMech.FrontierA.smearingStrictPositivePart_pos a v

/--
[smearingStrictNegativePart_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearingStrictNegativePart_pos_eq
  [Fintype V]
  {v : V}
-- given
  (a : V -> Real) :
-- imply
  0 < smearingStrictNegativePart a v := by
-- proof
  apply StatMech.FrontierA.smearingStrictNegativePart_pos a v

/--
[smearing_eq_strictPositivePart_sub_strictNegativePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma smearing_eq_strictPositivePart_sub_strictNegativePart_eq
  [Fintype V]
-- given
  (a : V -> Real) :
-- imply
  a = smearingStrictPositivePart a - smearingStrictNegativePart a := by
-- proof
  apply StatMech.FrontierA.smearing_eq_strictPositivePart_sub_strictNegativePart a

/--
[finiteWeightedCumulantLinePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma finiteWeightedCumulantLinePolynomial_eval_eq
  [Fintype V]
  {order : Nat}
  {r : Real}
-- given
  (ursell : (Fin order -> V) -> Real)
  (positive negative : V -> Real) :
-- imply
  (finiteWeightedCumulantLinePolynomial order ursell positive negative).eval r = finiteWeightedCumulant order ursell (positive + r • negative) := by
-- proof
  apply StatMech.FrontierA.finiteWeightedCumulantLinePolynomial_eval order ursell positive negative r

/--
[finiteWeightedCumulantLinePolynomial_natDegree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma finiteWeightedCumulantLinePolynomial_natDegree_le_eq
  [Fintype V]
  {order : Nat}
-- given
  (ursell : (Fin order -> V) -> Real)
  (positive negative : V -> Real) :
-- imply
  (finiteWeightedCumulantLinePolynomial order ursell positive negative).natDegree <= order := by
-- proof
  apply StatMech.FrontierA.finiteWeightedCumulantLinePolynomial_natDegree_le order ursell positive negative

/--
[finiteWeightedCumulantLinePolynomial_degree_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma finiteWeightedCumulantLinePolynomial_degree_lt_eq
  [Fintype V]
  {order : Nat}
-- given
  (ursell : (Fin order -> V) -> Real)
  (positive negative : V -> Real) :
-- imply
  (finiteWeightedCumulantLinePolynomial order ursell positive negative).degree < (order + 1 : Nat) := by
-- proof
  apply StatMech.FrontierA.finiteWeightedCumulantLinePolynomial_degree_lt order ursell positive negative

/--
[signedCumulant_tendsto_zero_of_nonnegative_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma signedCumulant_tendsto_zero_of_nonnegative_line_eq
  [AddCommGroup E]
  [Module Real E]
  {order : Nat}
  {positive negative signed : E}
-- given
  (cumulant : Nat -> E -> Real)
  (linePolynomial : Nat -> E -> E -> Real[X])
  (hdegree : forall scale positive negative, (linePolynomial scale positive negative).degree < (order + 1 : Nat))
  (heval : forall scale positive negative r, (linePolynomial scale positive negative).eval r = cumulant scale (positive + r • negative))
  (hsigned : signed = positive - negative)
  (hnodes : forall i : Fin (order + 1), Tendsto (fun scale => cumulant scale (positive + (((i : Nat) : Real) • negative))) atTop (nhds 0)) :
-- imply
  Tendsto (fun scale => cumulant scale signed) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.signedCumulant_tendsto_zero_of_nonnegative_line order cumulant linePolynomial hdegree heval positive negative signed hsigned hnodes

/--
[finiteWeightedCumulant_tendsto_zero_of_nonnegative_line](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianConePolarization.lean)
-/
@[path]
private lemma finiteWeightedCumulant_tendsto_zero_of_nonnegative_line_eq
  [Fintype V]
  {order : Nat}
-- given
  (ursell : Nat -> (Fin order -> V) -> Real)
  (positive negative signed : V -> Real)
  (hsigned : signed = positive - negative)
  (hnodes : forall i : Fin (order + 1), Tendsto (fun scale => finiteWeightedCumulant order (ursell scale) (positive + (((i : Nat) : Real) • negative))) atTop (nhds 0)) :
-- imply
  Tendsto (fun scale => finiteWeightedCumulant order (ursell scale) signed) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.finiteWeightedCumulant_tendsto_zero_of_nonnegative_line order ursell positive negative signed hsigned hnodes


-- created on 2026-10-23

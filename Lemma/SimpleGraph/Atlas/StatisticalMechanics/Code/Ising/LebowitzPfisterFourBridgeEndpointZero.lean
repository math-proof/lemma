import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
open Finset StatMech StatMech.Ising


/--
[ghsiSubsetMarginalMass_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma ghsiSubsetMarginalMass_logSupermodular_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {M P Q : Finset V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hPM : P ⊆ M)
  (hQM : Q ⊆ M) :
-- imply
  ghsiSubsetMarginalMass G K hf M P * ghsiSubsetMarginalMass G K hf M Q <= ghsiSubsetMarginalMass G K hf M (P ∩ Q) * ghsiSubsetMarginalMass G K hf M (P ∪ Q) := by
-- proof
  apply StatMech.Ising.ghsiSubsetMarginalMass_logSupermodular G K hf hK hhf hPM hQM

/--
[threePoint_strongGraham_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma threePoint_strongGraham_sum_eq
  [Fintype V]
  [DecidableEq V]
  {x y z p q s r : Real}
-- given
  (hx : 2 * x * p * q <= (1 - x ^ 2) * r)
  (hy : 2 * y * p * s <= (1 - y ^ 2) * r)
  (hz : 2 * z * q * s <= (1 - z ^ 2) * r) :
-- imply
  2 * (x * p * q + y * p * s + z * q * s) <= (3 - x ^ 2 - y ^ 2 - z ^ 2) * r := by
-- proof
  apply StatMech.Ising.threePoint_strongGraham_sum hx hy hz

/--
[threePoint_square_correction_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma threePoint_square_correction_le_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c r : Real}
-- given
  (hx : 0 <= x)
  (hy : 0 <= y)
  (hz : 0 <= z)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hr : 0 <= r)
  (hdelta : 0 <= x * y * z + x * c + y * b + z * a - r)
  (hstrong : 2 * (x * a * b + y * a * c + z * b * c) <= (3 - x ^ 2 - y ^ 2 - z ^ 2) * (x * y * z + x * c + y * b + z * a - r)) :
-- imply
  2 * (x * a * b * (x * y * z + y * b + z * a) + y * a * c * (x * y * z + x * c + z * a) + z * b * c * (x * y * z + x * c + y * b)) <= 3 * ((x * y * z + x * c + y * b + z * a) ^ 2 - r ^ 2) := by
-- proof
  apply StatMech.Ising.threePoint_square_correction_le hx hy hz ha hb hc hr hdelta hstrong

/--
[ghsiCovariance_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma ghsiCovariance_comm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiCovariance G K hf i j = ghsiCovariance G K hf j i := by
-- proof
  apply StatMech.Ising.ghsiCovariance_comm G K hf i j

/--
[ghsiUrsell3_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma ghsiUrsell3_cyclic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiUrsell3 G K hf i j k = ghsiUrsell3 G K hf j k i := by
-- proof
  apply StatMech.Ising.ghsiUrsell3_cyclic G K hf i j k

/--
[ghsiUrsell3_swap_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma ghsiUrsell3_swap_last_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  ghsiUrsell3 G K hf i j k = ghsiUrsell3 G K hf i k j := by
-- proof
  apply StatMech.Ising.ghsiUrsell3_swap_last G K hf i j k

/--
[grahamInhomThreePoint_strong_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma grahamInhomThreePoint_strong_symmetric_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  2 * (grahamInhomOne G K hf i * ghsiCovariance G K hf i j * ghsiCovariance G K hf i k + grahamInhomOne G K hf j * ghsiCovariance G K hf i j * ghsiCovariance G K hf j k + grahamInhomOne G K hf k * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k) <= (3 - grahamInhomOne G K hf i ^ 2 - grahamInhomOne G K hf j ^ 2 - grahamInhomOne G K hf k ^ 2) * (-ghsiUrsell3 G K hf i j k) := by
-- proof
  apply StatMech.Ising.grahamInhomThreePoint_strong_symmetric G K hf hK hhf i j k

/--
[grahamInhomThreePoint_square_correction_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma grahamInhomThreePoint_square_correction_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  let mi := grahamInhomOne G K hf i let mj := grahamInhomOne G K hf j let mk := grahamInhomOne G K hf k let cij := ghsiCovariance G K hf i j let cik := ghsiCovariance G K hf i k let cjk := ghsiCovariance G K hf j k let r := expJ G.edgeFinset K hf (fun s => spin s i * (spin s j * spin s k)) let u := mi * mj * mk + mi * cjk + mj * cik + mk * cij 2 * (mi * cij * cik * (mi * mj * mk + mj * cik + mk * cij) + mj * cij * cjk * (mi * mj * mk + mi * cjk + mk * cij) + mk * cik * cjk * (mi * mj * mk + mi * cjk + mj * cik)) <= 3 * (u ^ 2 - r ^ 2) := by
-- proof
  apply StatMech.Ising.grahamInhomThreePoint_square_correction_le G K hf hK hhf hij hik hjk

/--
[grahamInhom_pair_covariance_square_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma grahamInhom_pair_covariance_square_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall x, 0 <= hf x) :
-- imply
  grahamInhomOne G K hf i * ghsiCovariance G K hf i j ^ 2 <= (1 - grahamInhomOne G K hf i ^ 2) * grahamInhomOne G K hf j * ghsiCovariance G K hf i j := by
-- proof
  apply StatMech.Ising.grahamInhom_pair_covariance_square_le G K hf hK hhf i j

/--
[expJ_variance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma expJ_variance_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (f : ConfigSpace V -> Real) :
-- imply
  0 <= expJ G.edgeFinset K hf (fun s => f s ^ 2) - expJ G.edgeFinset K hf f ^ 2 := by
-- proof
  apply StatMech.Ising.expJ_variance_nonneg G K hf f

/--
[ghsiCovariance_quadratic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma ghsiCovariance_quadratic_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (K : Sym2 V -> Real)
  (hf dir : V -> Real) :
-- imply
  0 <= ∑ i : V, ∑ j : V, dir i * dir j * ghsiCovariance G K hf i j := by
-- proof
  apply StatMech.Ising.ghsiCovariance_quadratic_nonneg G K hf dir

/--
[fourBridge_zero_base_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_zero_base_identity_eq
  [Fintype V]
  [DecidableEq V]
  {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real} :
-- imply
  let p01 := m0 * m1 + c01 let p02 := m0 * m2 + c02 let p03 := m0 * m3 + c03 let p12 := m1 * m2 + c12 let p13 := m1 * m3 + c13 let p23 := m2 * m3 + c23 let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2 let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3 let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3 let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3 let a := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 let b := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2 a + 3 * a * b - a ^ 3 - 3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) = m0 ^ 2 * (1 - m0 ^ 4) + 6 * m0 ^ 3 * (c01 * m1 + c02 * m2 + c03 * m3) + 6 * (c01 ^ 2 * m1 ^ 2 + c02 ^ 2 * m2 ^ 2 + c03 ^ 2 * m3 ^ 2) - 3 * (c01 * m1 + c02 * m2 + c03 * m3) ^ 2 + m1 ^ 2 * (1 - m1 ^ 4) + 6 * m1 ^ 3 * (c01 * m0 + c12 * m2 + c13 * m3) + 6 * (c01 ^ 2 * m0 ^ 2 + c12 ^ 2 * m2 ^ 2 + c13 ^ 2 * m3 ^ 2) - 3 * (c01 * m0 + c12 * m2 + c13 * m3) ^ 2 + m2 ^ 2 * (1 - m2 ^ 4) + 6 * m2 ^ 3 * (c02 * m0 + c12 * m1 + c23 * m3) + 6 * (c02 ^ 2 * m0 ^ 2 + c12 ^ 2 * m1 ^ 2 + c23 ^ 2 * m3 ^ 2) - 3 * (c02 * m0 + c12 * m1 + c23 * m3) ^ 2 + m3 ^ 2 * (1 - m3 ^ 4) + 6 * m3 ^ 3 * (c03 * m0 + c13 * m1 + c23 * m2) + 6 * (c03 ^ 2 * m0 ^ 2 + c13 ^ 2 * m1 ^ 2 + c23 ^ 2 * m2 ^ 2) - 3 * (c03 * m0 + c13 * m1 + c23 * m2) ^ 2 := by
-- proof
  apply StatMech.Ising.fourBridge_zero_base_identity m0 m1 m2 m3 c01 c02 c03 c12 c13 c23

/--
[covariancePSD_row_contraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma covariancePSD_row_contraction_eq
  [Fintype V]
  [DecidableEq V]
  {m x y z a b c d e f : Real}
-- given
  (hpsd : forall q0 q1 q2 q3 : Real, 0 <= (1 - m ^ 2) * q0 ^ 2 + (1 - x ^ 2) * q1 ^ 2 + (1 - y ^ 2) * q2 ^ 2 + (1 - z ^ 2) * q3 ^ 2 + 2 * a * q0 * q1 + 2 * b * q0 * q2 + 2 * c * q0 * q3 + 2 * d * q1 * q2 + 2 * e * q1 * q3 + 2 * f * q2 * q3) :
-- imply
  let s := a * x + b * y + c * z (1 + m ^ 2) * s ^ 2 <= (1 - x ^ 2) * x ^ 2 + (1 - y ^ 2) * y ^ 2 + (1 - z ^ 2) * z ^ 2 + 2 * d * x * y + 2 * e * x * z + 2 * f * y * z := by
-- proof
  apply StatMech.Ising.covariancePSD_row_contraction hpsd

/--
[covariancePSD_three_det_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma covariancePSD_three_det_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hpsd : forall q0 q1 q2 : Real, 0 <= (1 - x ^ 2) * q0 ^ 2 + (1 - y ^ 2) * q1 ^ 2 + (1 - z ^ 2) * q2 ^ 2 + 2 * a * q0 * q1 + 2 * b * q0 * q2 + 2 * c * q1 * q2) :
-- imply
  0 <= (1 - x ^ 2) * (1 - y ^ 2) * (1 - z ^ 2) + 2 * a * b * c - (1 - x ^ 2) * c ^ 2 - (1 - y ^ 2) * b ^ 2 - (1 - z ^ 2) * a ^ 2 := by
-- proof
  apply StatMech.Ising.covariancePSD_three_det_nonneg hpsd

/--
[twoVar_cubic_edge_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  0 <= 1 + 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_nonneg ha0 hb0

/--
[twoVar_cubic_edge_linear_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_linear_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  0 <= a + b + 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_linear_nonneg ha0 hb0

/--
[twoVar_cubic_edge_three_quarters_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_three_quarters_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  0 <= 3 / 4 + 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_three_quarters_nonneg ha0 hb0

/--
[twoVar_cubic_edge_left_linear_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_left_linear_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  0 <= 27 / 8 * a + 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_left_linear_nonneg ha0 hb0

/--
[twoVar_cubic_edge_sum_linear_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_sum_linear_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  0 <= 27 / 32 * (a + b) + 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_sum_linear_nonneg ha0 hb0

/--
[twoVar_cubic_edge_min_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma twoVar_cubic_edge_min_cost_eq
  [Fintype V]
  [DecidableEq V]
  {a b : Real}
-- given
  (ha0 : 0 <= a)
  (hb0 : 0 <= b) :
-- imply
  -(min (3 / 4) (min (27 / 8 * min a b) (27 / 32 * (a + b)))) <= 6 * a * b * (a + b) - 9 * a * b := by
-- proof
  apply StatMech.Ising.twoVar_cubic_edge_min_cost ha0 hb0

/--
[pair_covariance_square_bound_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma pair_covariance_square_bound_cancel_eq
  [Fintype V]
  [DecidableEq V]
  {x y a : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hx1 : x <= 1)
  (ha : 0 <= a)
  (h : x * a ^ 2 <= (1 - x ^ 2) * y * a) :
-- imply
  x * a <= (1 - x ^ 2) * y := by
-- proof
  apply StatMech.Ising.pair_covariance_square_bound_cancel hx0 hy0 hx1 ha h

/--
[fourBridge_triangle_cross_remainder_nonneg_of_sqsum_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_triangle_cross_remainder_nonneg_of_sqsum_ge_one_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
  (hS : 1 <= x ^ 2 + y ^ 2 + z ^ 2) :
-- imply
  9 * (a * b * y * z + a * c * x * z + b * c * x * y) <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 6 * x * a * b * (x * y * z + y * b + z * a) + 6 * y * a * c * (x * y * z + x * c + z * a) + 6 * z * b * c * (x * y * z + x * c + y * b) := by
-- proof
  apply StatMech.Ising.fourBridge_triangle_cross_remainder_nonneg_of_sqsum_ge_one hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc hS

/--
[fourBridge_triangle_correct_nonneg_of_sqsum_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_triangle_correct_nonneg_of_sqsum_ge_one_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
  (hS : 1 <= x ^ 2 + y ^ 2 + z ^ 2) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.fourBridge_triangle_correct_nonneg_of_sqsum_ge_one hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc hS

/--
[fourBridge_triangle_correct_nonneg_of_first_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_triangle_correct_nonneg_of_first_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hx : x = 0) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.fourBridge_triangle_correct_nonneg_of_first_eq_zero hx0 hy0 hz0 hy1 hz1 ha hb hc hya hzb hx

/--
[fourBridge_triangle_correct_nonneg_of_any_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_triangle_correct_nonneg_of_any_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
  (hzero : x = 0 ∨ y = 0 ∨ z = 0) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.fourBridge_triangle_correct_nonneg_of_any_eq_zero hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc hzero

/--
[fourBridge_triangle_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_triangle_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.fourBridge_triangle_nonneg hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc

/--
[fourBridge_Ursell_correction_nonneg_of_face_sqsum_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_Ursell_correction_nonneg_of_face_sqsum_ge_one_eq
  [Fintype V]
  [DecidableEq V]
  {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
-- given
  (hm00 : 0 <= m0)
  (hm10 : 0 <= m1)
  (hm20 : 0 <= m2)
  (hm30 : 0 <= m3)
  (hm01 : m0 <= 1)
  (hm11 : m1 <= 1)
  (hm21 : m2 <= 1)
  (hm31 : m3 <= 1)
  (hc01 : 0 <= c01)
  (hc02 : 0 <= c02)
  (hc03 : 0 <= c03)
  (hc12 : 0 <= c12)
  (hc13 : 0 <= c13)
  (hc23 : 0 <= c23)
  (h001 : m0 * c01 ^ 2 <= (1 - m0 ^ 2) * m1 * c01)
  (h101 : m1 * c01 ^ 2 <= (1 - m1 ^ 2) * m0 * c01)
  (h002 : m0 * c02 ^ 2 <= (1 - m0 ^ 2) * m2 * c02)
  (h202 : m2 * c02 ^ 2 <= (1 - m2 ^ 2) * m0 * c02)
  (h003 : m0 * c03 ^ 2 <= (1 - m0 ^ 2) * m3 * c03)
  (h303 : m3 * c03 ^ 2 <= (1 - m3 ^ 2) * m0 * c03)
  (h112 : m1 * c12 ^ 2 <= (1 - m1 ^ 2) * m2 * c12)
  (h212 : m2 * c12 ^ 2 <= (1 - m2 ^ 2) * m1 * c12)
  (h113 : m1 * c13 ^ 2 <= (1 - m1 ^ 2) * m3 * c13)
  (h313 : m3 * c13 ^ 2 <= (1 - m3 ^ 2) * m1 * c13)
  (h223 : m2 * c23 ^ 2 <= (1 - m2 ^ 2) * m3 * c23)
  (h323 : m3 * c23 ^ 2 <= (1 - m3 ^ 2) * m2 * c23)
  (h012S : 1 <= m0 ^ 2 + m1 ^ 2 + m2 ^ 2)
  (h013S : 1 <= m0 ^ 2 + m1 ^ 2 + m3 ^ 2)
  (h023S : 1 <= m0 ^ 2 + m2 ^ 2 + m3 ^ 2)
  (h123S : 1 <= m1 ^ 2 + m2 ^ 2 + m3 ^ 2) :
-- imply
  let p01 := m0 * m1 + c01 let p02 := m0 * m2 + c02 let p03 := m0 * m3 + c03 let p12 := m1 * m2 + c12 let p13 := m1 * m3 + c13 let p23 := m2 * m3 + c23 let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2 let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3 let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3 let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3 let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2 0 <= aa + 3 * aa * bb - aa ^ 3 - 3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) + 2 * (m0 * c01 * c02 * (m0 * m1 * m2 + m1 * c02 + m2 * c01) + m1 * c01 * c12 * (m0 * m1 * m2 + m0 * c12 + m2 * c01) + m2 * c02 * c12 * (m0 * m1 * m2 + m0 * c12 + m1 * c02)) + 2 * (m0 * c01 * c03 * (m0 * m1 * m3 + m1 * c03 + m3 * c01) + m1 * c01 * c13 * (m0 * m1 * m3 + m0 * c13 + m3 * c01) + m3 * c03 * c13 * (m0 * m1 * m3 + m0 * c13 + m1 * c03)) + 2 * (m0 * c02 * c03 * (m0 * m2 * m3 + m2 * c03 + m3 * c02) + m2 * c02 * c23 * (m0 * m2 * m3 + m0 * c23 + m3 * c02) + m3 * c03 * c23 * (m0 * m2 * m3 + m0 * c23 + m2 * c03)) + 2 * (m1 * c12 * c13 * (m1 * m2 * m3 + m2 * c13 + m3 * c12) + m2 * c12 * c23 * (m1 * m2 * m3 + m1 * c23 + m3 * c12) + m3 * c13 * c23 * (m1 * m2 * m3 + m1 * c23 + m2 * c13)) := by
-- proof
  apply StatMech.Ising.fourBridge_Ursell_correction_nonneg_of_face_sqsum_ge_one hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31 hc01 hc02 hc03 hc12 hc13 hc23 h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323 h012S h013S h023S h123S

/--
[fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos_of_face_sqsum_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos_of_face_sqsum_ge_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall v, 0 <= hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z)
  (h012S : 1 <= grahamInhomOne G K hf w ^ 2 + grahamInhomOne G K hf x ^ 2 + grahamInhomOne G K hf y ^ 2)
  (h013S : 1 <= grahamInhomOne G K hf w ^ 2 + grahamInhomOne G K hf x ^ 2 + grahamInhomOne G K hf z ^ 2)
  (h023S : 1 <= grahamInhomOne G K hf w ^ 2 + grahamInhomOne G K hf y ^ 2 + grahamInhomOne G K hf z ^ 2)
  (h123S : 1 <= grahamInhomOne G K hf x ^ 2 + grahamInhomOne G K hf y ^ 2 + grahamInhomOne G K hf z ^ 2) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G K hf w x y z) (fourBridgeTwoCoeff G K hf w x y z) (fourBridgeThreeCoeff G K hf w x y z) (fourBridgeFourCoeff G K hf w x y z) 0 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos_of_face_sqsum_ge_one G K hf hK hhf hwx hwy hwz hxy hxz hyz h012S h013S h023S h123S

/--
[fourBridge_Ursell_correction_with_edgeSlack_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeEndpointZero.lean)
-/
@[path]
private lemma fourBridge_Ursell_correction_with_edgeSlack_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
-- given
  (hm00 : 0 <= m0)
  (hm10 : 0 <= m1)
  (hm20 : 0 <= m2)
  (hm30 : 0 <= m3)
  (hm01 : m0 <= 1)
  (hm11 : m1 <= 1)
  (hm21 : m2 <= 1)
  (hm31 : m3 <= 1)
  (hc01 : 0 <= c01)
  (hc02 : 0 <= c02)
  (hc03 : 0 <= c03)
  (hc12 : 0 <= c12)
  (hc13 : 0 <= c13)
  (hc23 : 0 <= c23) :
-- imply
  let p01 := m0 * m1 + c01 let p02 := m0 * m2 + c02 let p03 := m0 * m3 + c03 let p12 := m1 * m2 + c12 let p13 := m1 * m3 + c13 let p23 := m2 * m3 + c23 let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2 let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3 let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3 let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3 let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2 0 <= aa + 3 * aa * bb - aa ^ 3 - 3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) + 2 * (m0 * c01 * c02 * (m0 * m1 * m2 + m1 * c02 + m2 * c01) + m1 * c01 * c12 * (m0 * m1 * m2 + m0 * c12 + m2 * c01) + m2 * c02 * c12 * (m0 * m1 * m2 + m0 * c12 + m1 * c02)) + 2 * (m0 * c01 * c03 * (m0 * m1 * m3 + m1 * c03 + m3 * c01) + m1 * c01 * c13 * (m0 * m1 * m3 + m0 * c13 + m3 * c01) + m3 * c03 * c13 * (m0 * m1 * m3 + m0 * c13 + m1 * c03)) + 2 * (m0 * c02 * c03 * (m0 * m2 * m3 + m2 * c03 + m3 * c02) + m2 * c02 * c23 * (m0 * m2 * m3 + m0 * c23 + m3 * c02) + m3 * c03 * c23 * (m0 * m2 * m3 + m0 * c23 + m2 * c03)) + 2 * (m1 * c12 * c13 * (m1 * m2 * m3 + m2 * c13 + m3 * c12) + m2 * c12 * c23 * (m1 * m2 * m3 + m1 * c23 + m3 * c12) + m3 * c13 * c23 * (m1 * m2 * m3 + m1 * c23 + m2 * c13)) + 3 * (c01 ^ 2 * (m0 ^ 2 + m1 ^ 2) + c02 ^ 2 * (m0 ^ 2 + m2 ^ 2) + c03 ^ 2 * (m0 ^ 2 + m3 ^ 2) + c12 ^ 2 * (m1 ^ 2 + m2 ^ 2) + c13 ^ 2 * (m1 ^ 2 + m3 ^ 2) + c23 ^ 2 * (m2 ^ 2 + m3 ^ 2)) := by
-- proof
  apply StatMech.Ising.fourBridge_Ursell_correction_with_edgeSlack_nonneg hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31 hc01 hc02 hc03 hc12 hc13 hc23


-- created on 2026-10-23

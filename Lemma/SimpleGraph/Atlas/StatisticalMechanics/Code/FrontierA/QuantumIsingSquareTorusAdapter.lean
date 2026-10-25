import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSquareTorusAdapter.Part7
open StatMech StatMech.FrontierA


/--
[squareTorusPositiveDirection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma squareTorusPositiveDirection_zero_eq :
-- imply
  squareTorusPositiveDirection 0 = 0 := by
-- proof
  apply StatMech.FrontierA.squareTorusPositiveDirection_zero

/--
[squareTorusPositiveDirection_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma squareTorusPositiveDirection_one_eq :
-- imply
  squareTorusPositiveDirection 1 = 1 := by
-- proof
  apply StatMech.FrontierA.squareTorusPositiveDirection_one

/--
[squareTorusPositiveEdgeMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma squareTorusPositiveEdgeMap_injective_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Injective (squareTorusPositiveEdgeMap L) := by
-- proof
  apply StatMech.FrontierA.squareTorusPositiveEdgeMap_injective L

/--
[squareTorusPositiveEdgeMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma squareTorusPositiveEdgeMap_surjective_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Surjective (squareTorusPositiveEdgeMap L) := by
-- proof
  apply StatMech.FrontierA.squareTorusPositiveEdgeMap_surjective L

/--
[sum_squareTorus_edges_eq_positive_directions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma sum_squareTorus_edges_eq_positive_directions_eq
  {L : Nat}
  [Fact (2 < L)]
  {f : Sym2 (ZMod L × ZMod L) → Real} :
-- imply
  (∑ edge ∈ (onsTorusGraph L).edgeFinset, f edge) = ∑ p : ZMod L × ZMod L, (f (ons_portEdge L (p, 0)) + f (ons_portEdge L (p, 1))) := by
-- proof
  apply StatMech.FrontierA.sum_squareTorus_edges_eq_positive_directions L f

/--
[prod_squareTorus_edges_eq_positive_directions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma prod_squareTorus_edges_eq_positive_directions_eq
  {L : Nat}
  [Fact (2 < L)]
  {f : Sym2 (ZMod L × ZMod L) → Real} :
-- imply
  (∏ edge ∈ (onsTorusGraph L).edgeFinset, f edge) = ∏ p : ZMod L × ZMod L, (f (ons_portEdge L (p, 0)) * f (ons_portEdge L (p, 1))) := by
-- proof
  apply StatMech.FrontierA.prod_squareTorus_edges_eq_positive_directions L f

/--
[quantumIsingSquareConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingSquareConfigEquiv_apply_eq
  {L : Nat}
  [NeZero L]
  {omega : Fin L → QuantumIsingChainConfig L}
  {k i : Fin L} :
-- imply
  quantumIsingSquareConfigEquiv L omega (ZMod.finEquiv L i, ZMod.finEquiv L k) = omega k i := by
-- proof
  apply StatMech.FrontierA.quantumIsingSquareConfigEquiv_apply L omega k i

/--
[finEquiv_quantumIsingCyclicSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma finEquiv_quantumIsingCyclicSucc_eq
  {L : Nat}
  [NeZero L]
  {i : Fin L} :
-- imply
  ZMod.finEquiv L (quantumIsingCyclicSucc i) = ZMod.finEquiv L i + 1 := by
-- proof
  apply StatMech.FrontierA.finEquiv_quantumIsingCyclicSucc L i

/--
[quantumIsingSquareTorusCoupling_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingSquareTorusCoupling_horizontal_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L}
-- given
  (beta h : Real) :
-- imply
  quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 0)) = beta / (4 * L) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSquareTorusCoupling_horizontal beta h L p

/--
[quantumIsingSquareTorusCoupling_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingSquareTorusCoupling_vertical_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L}
-- given
  (beta h : Real) :
-- imply
  quantumIsingSquareTorusCoupling beta h L (ons_portEdge L (p, 1)) = quantumIsingVerticalCoupling beta h L := by
-- proof
  apply StatMech.FrontierA.quantumIsingSquareTorusCoupling_vertical beta h L p

/--
[sum_zmod_square_eq_fin_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma sum_zmod_square_eq_fin_square_eq
  {L : Nat}
  [NeZero L]
  {f : ZMod L × ZMod L → Real} :
-- imply
  (∑ p : ZMod L × ZMod L, f p) = ∑ k : Fin L, ∑ i : Fin L, f (ZMod.finEquiv L i, ZMod.finEquiv L k) := by
-- proof
  apply StatMech.FrontierA.sum_zmod_square_eq_fin_square L f

/--
[quantumIsingSquareTorus_energy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingSquareTorus_energy_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {omega : Fin L → QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  (∑ edge ∈ (onsTorusGraph L).edgeFinset, quantumIsingSquareTorusCoupling beta h L edge * bond (quantumIsingSquareConfigEquiv L omega) edge) = quantumIsingSquareTrotterEnergy beta h L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingSquareTorus_energy_eq beta h L omega

/--
[quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy_eq
  {L : Nat}
  {omega : Fin L → QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderWeight beta h L L omega = Real.exp (quantumIsingSquareTrotterEnergy beta h L omega) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderWeight_diagonal_eq_exp_energy beta h L omega

/--
[quantumIsingClassicalCylinderWeight_eq_torus_wJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderWeight_eq_torus_wJ_eq
  {L : Nat}
  [Fact (2 < L)]
  {omega : Fin L → QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderWeight beta h L L omega = StatMech.Sharpness.wJ (onsTorusGraph L).edgeFinset (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0) (quantumIsingSquareConfigEquiv L omega) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderWeight_eq_torus_wJ beta h L omega

/--
[quantumIsingClassicalCylinderPartition_eq_torus_ZJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_eq_torus_ZJ_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderPartition beta h L L = StatMech.Sharpness.ZJ (onsTorusGraph L).edgeFinset (quantumIsingSquareTorusCoupling beta h L) (fun _ ↦ 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_eq_torus_ZJ beta h L

/--
[tanh_quantumIsingSquareTorusCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma tanh_quantumIsingSquareTorusCoupling_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  (fun edge ↦ Real.tanh (quantumIsingSquareTorusCoupling beta h L edge)) = quantumIsingSquareTorusTanhWeight beta h L := by
-- proof
  apply StatMech.FrontierA.tanh_quantumIsingSquareTorusCoupling beta h L

/--
[coe_quantumIsingSquareTorusTanhWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma coe_quantumIsingSquareTorusTanhWeight_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  (fun edge ↦ (quantumIsingSquareTorusTanhWeight beta h L edge : Complex)) = anisotropicSquareEdgeWeight L (Real.tanh (beta / (4 * L))) (Real.tanh (quantumIsingVerticalCoupling beta h L)) := by
-- proof
  apply StatMech.FrontierA.coe_quantumIsingSquareTorusTanhWeight beta h L

/--
[prod_cosh_quantumIsingSquareTorusCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma prod_cosh_quantumIsingSquareTorusCoupling_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  (∏ edge ∈ (onsTorusGraph L).edgeFinset, Real.cosh (quantumIsingSquareTorusCoupling beta h L edge)) = (Real.cosh (beta / (4 * L)) * Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) := by
-- proof
  apply StatMech.FrontierA.prod_cosh_quantumIsingSquareTorusCoupling beta h L

/--
[quantumIsingClassicalCylinderPartition_highTemperature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_highTemperature_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderPartition beta h L L = (2 : Real) ^ (L * L) * (Real.cosh (beta / (4 * L)) * Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) * inhomogeneousEvenSubgraphSum (onsTorusGraph L) (quantumIsingSquareTorusTanhWeight beta h L) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_highTemperature beta h L

/--
[two_mul_quantumIsingClassicalCylinderPartition_eq_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSquareTorusAdapter.lean)
-/
@[path]
private lemma two_mul_quantumIsingClassicalCylinderPartition_eq_spin_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real) :
-- imply
  (2 : Complex) * quantumIsingClassicalCylinderPartition beta h L L = ((2 : Real) ^ (L * L) * (Real.cosh (beta / (4 * L)) * Real.cosh (quantumIsingVerticalCoupling beta h L)) ^ (L * L) : Real) * (ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh (beta / (4 * L))) (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 1 + ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh (beta / (4 * L))) (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 1 + ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh (beta / (4 * L))) (Real.tanh (quantumIsingVerticalCoupling beta h L))) 1 0 - ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh (beta / (4 * L))) (Real.tanh (quantumIsingVerticalCoupling beta h L))) 0 0) := by
-- proof
  apply StatMech.FrontierA.two_mul_quantumIsingClassicalCylinderPartition_eq_spin beta h L


-- created on 2026-10-23

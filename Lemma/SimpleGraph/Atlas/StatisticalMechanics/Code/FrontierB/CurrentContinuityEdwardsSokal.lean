import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityEdwardsSokal
open Filter MeasureTheory Set StatMech StatMech.FrontierB


/--
[monoIndicator_pair_eq_half_one_add_esSpinProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma monoIndicator_pair_eq_half_one_add_esSpinProduct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {sigma : V → Fin 2}
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  Potts.monoIndicator sigma s(x, y) = (1 + esSpinProduct ({x, y} : Finset V) sigma) / 2 := by
-- proof
  apply StatMech.FrontierB.monoIndicator_pair_eq_half_one_add_esSpinProduct G sigma x y hxy

/--
[esMonoExpectation_eq_half_one_add_isingExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma esMonoExpectation_eq_half_one_add_isingExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  (∑ sigma : V → Fin 2, esFirstMarginal G 2 (1 - Real.exp (-2 * beta)) sigma * Potts.monoIndicator sigma s(x, y)) = (1 + Ising.isingExpectation G beta 0 (spinProd ({x, y} : Finset V))) / 2 := by
-- proof
  apply StatMech.FrontierB.esMonoExpectation_eq_half_one_add_isingExpectation G beta x y hxy

/--
[edgeMargProb_fkProb_eq_p_div_two_mul_one_add_isingExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma edgeMargProb_fkProb_eq_p_div_two_mul_one_add_isingExpectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {x y : V}
-- given
  (hxy : x ≠ y)
  (hedge : s(x, y) ∈ G.edgeFinset) :
-- imply
  edgeMargProb (fkProb G (1 - Real.exp (-2 * beta)) 2) s(x, y) = (1 - Real.exp (-2 * beta)) / 2 * (1 + Ising.isingExpectation G beta 0 (spinProd ({x, y} : Finset V))) := by
-- proof
  apply StatMech.FrontierB.edgeMargProb_fkProb_eq_p_div_two_mul_one_add_isingExpectation G beta x y hxy hedge

/--
[esWeightWired_open_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma esWeightWired_open_sum_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {beta : Real}
  {sigma : V → Fin 2}
  {x y : V}
-- given
  (bdry : V → Prop)
  (hedge : s(x, y) ∈ G.edgeFinset) :
-- imply
  (∑ omega : ConfigSpace (Sym2 V), esWeightWired G bdry (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma omega * (if omega s(x, y) then 1 else 0)) = (1 - Real.exp (-2 * beta)) * Potts.monoIndicator sigma s(x, y) * ∑ omega : ConfigSpace (Sym2 V), esWeightWired G bdry (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma omega := by
-- proof
  apply StatMech.FrontierB.esWeightWired_open_sum_eq G bdry beta sigma x y hedge

/--
[edgeMargProb_wiredFkProb_eq_p_mul_esWiredMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma edgeMargProb_wiredFkProb_eq_p_mul_esWiredMono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {v0 : V}
  {beta : Real}
  {x y : V}
-- given
  (bdry : V → Prop)
  (hv0 : bdry v0)
  (hedge : s(x, y) ∈ G.edgeFinset) :
-- imply
  edgeMargProb (wiredFkProb G bdry (1 - Real.exp (-2 * beta)) 2) s(x, y) = (1 - Real.exp (-2 * beta)) * ∑ sigma : V → Fin 2, esWiredFirstMarginal G bdry 2 (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma * Potts.monoIndicator sigma s(x, y) := by
-- proof
  apply StatMech.FrontierB.edgeMargProb_wiredFkProb_eq_p_mul_esWiredMono G bdry v0 hv0 beta x y hedge

/--
[hbx_isingWiredPair_eq_plusIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma hbx_isingWiredPair_eq_plusIntegral_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {beta : Real}
  {x y : boxVerts d n}
-- given
  (hxy : x ≠ y) :
-- imply
  ((∑ sigma : boxVerts d (n + 1) → Fin 2, isingWiredWeight (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta sigma * esSpinProduct ({boxSiteSucc x, boxSiteSucc y} : Finset (boxVerts d (n + 1))) sigma) / isingWiredZ (boxGraph d (n + 1)) (boxBoundary d (n + 1)) beta) = ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.FrontierB.hbx_isingWiredPair_eq_plusIntegral G d n beta x y hxy

/--
[esWiredMonoExpectation_box_eq_half_one_add_plusIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma esWiredMonoExpectation_box_eq_half_one_add_plusIntegral_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {beta : Real}
  {x y : boxVerts d n}
-- given
  (hxy : x ≠ y) :
-- imply
  (∑ sigma : boxVerts d (n + 1) → Fin 2, esWiredFirstMarginal (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2 (0 : Fin 2) (1 - Real.exp (-2 * beta)) sigma * Potts.monoIndicator sigma s(boxSiteSucc x, boxSiteSucc y)) = (1 + ∫ omega, spinProd ({x.1, y.1} : Finset (Site d)) omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) / 2 := by
-- proof
  apply StatMech.FrontierB.esWiredMonoExpectation_box_eq_half_one_add_plusIntegral G d n beta x y hxy

/--
[freeEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityFreeTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma freeEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityFreeTwoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {N : Nat}
  {beta : Real}
  {x y : boxVerts d N}
-- given
  (hbeta : 0 < beta)
  (hxy : (boxGraph d N).Adj x y) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N s(x, y)) (1 - Real.exp (-2 * beta)) = (1 - Real.exp (-2 * beta)) / 2 * (1 + currentContinuityFreeTwoPoint d beta x.1 y.1) := by
-- proof
  apply StatMech.FrontierB.freeEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityFreeTwoPoint G N beta hbeta x y hxy

/--
[wiredEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityPlusTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma wiredEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityPlusTwoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {N : Nat}
  {beta : Real}
  {x y : boxVerts d N}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hxy : (boxGraph d N).Adj x y) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N s(x, y)) (1 - Real.exp (-2 * beta)) = (1 - Real.exp (-2 * beta)) / 2 * (1 + currentContinuityPlusTwoPoint d beta x.1 y.1) := by
-- proof
  apply StatMech.FrontierB.wiredEdgeDensity_eq_p_div_two_mul_one_add_currentContinuityPlusTwoPoint G N beta hbeta hd x y hxy

/--
[currentContinuity_allEdgeDensity_eq_of_adjacent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma currentContinuity_allEdgeDensity_eq_of_adjacent_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hadj : ∀ x y : Site d, (hypercubicLattice d).Adj x y → currentContinuityPlusTwoPoint d beta x y = currentContinuityFreeTwoPoint d beta x y) :
-- imply
  ∀ (N : Nat) (e : Sym2 (boxVerts d N)), freeEdgeDensity d 2 (edgeIncl d N e) (1 - Real.exp (-2 * beta)) = wiredEdgeDensity d 2 (edgeIncl d N e) (1 - Real.exp (-2 * beta)) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_allEdgeDensity_eq_of_adjacent_eq G beta hbeta hd hadj

/--
[currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hnoperco : (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (Percolation.percolationEvent d) = 0) :
-- imply
  (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_freeInfiniteVolume_eq_wiredInfiniteVolume_of_noPercolation G beta hbeta hd hnoperco

/--
[currentContinuity_FK_phase_eq_of_freeLROZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityEdwardsSokal.lean)
-/
@[path]
private lemma currentContinuity_FK_phase_eq_of_freeLROZero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (hLRO : CurrentContinuityFreeLROZero d beta) :
-- imply
  (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real (Percolation.percolationEvent d) = 0 ∧ (freeInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) = (wiredInfiniteVolume d (p := 1 - Real.exp (-2 * beta)) (q := 2) (by exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) (by linarith [Real.exp_pos (-2 * beta)]) (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuity_FK_phase_eq_of_freeLROZero G beta hbeta hd hLRO


-- created on 2026-10-23

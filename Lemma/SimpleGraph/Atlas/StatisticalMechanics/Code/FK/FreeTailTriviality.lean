import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FreeTailTriviality
open MeasureTheory ProbabilityTheory Set Filter Topology StatMech StatMech.FK


/--
[freeInner_mul_outside_le_bcProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInner_mul_outside_le_bcProb_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {C : SimpleGraph Vout}
  [DecidableRel C.Adj]
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 Vin))}
  {B : Set (ConfigSpace (Sym2 Vout))}
-- given
  (hι : Function.Injective ιV)
  (hadj : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := Vin) ιV) B) :
-- imply
  (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega * fkProb Gin p q omega) * (∑ rho, B.indicator (fun _ => (1 : ℝ)) rho * bcProb Gout C p q rho) ≤ ∑ rho, ((ocd_innerRestrict ιV ⁻¹' A) ∩ B).indicator (fun _ => (1 : ℝ)) rho * bcProb Gout C p q rho := by
-- proof
  apply StatMech.FK.freeInner_mul_outside_le_bcProb Gin Gout ιV hι hadj C hp hp1 hq hA hB

/--
[isFKDLR_freeMass_mul_outside_le_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma isFKDLR_freeMass_mul_outside_le_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
  {B : Set (ConfigSpace (Sym2 (boxVerts d m)))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : IsFKDLR d p q phi)
  (hA : IsIncreasing A)
  (hB : DependsOnOutside (ocd_innerEdgeFinset (Vin := boxVerts d N) (boxVertInclLE d (le_of_lt hNm))) B) :
-- imply
  dlrBcEventMass (boxGraph d N) (⊥ : SimpleGraph (boxVerts d N)) p q A * (phi : Measure _).real (boxRestrict d m ⁻¹' B) ≤ (phi : Measure _).real (boxRestrict d m ⁻¹' ((ocd_innerRestrict (boxVertInclLE d (le_of_lt hNm)) ⁻¹' A) ∩ B)) := by
-- proof
  apply StatMech.FK.isFKDLR_freeMass_mul_outside_le_generalQ hNm hp hp1 hq phi hphi hA hB

/--
[edgeIncl_mem_fkTailEdgeWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma edgeIncl_mem_fkTailEdgeWindow_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  edgeIncl d N eb ∈ fkTailEdgeWindow d N := by
-- proof
  apply StatMech.FK.edgeIncl_mem_fkTailEdgeWindow N eb

/--
[exteriorCylinder_realise_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma exteriorCylinder_realise_in_box_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N : ℕ}
  {F : Finset (Sym2 (Site d))}
  {S : Set (ConfigSpace F)}
-- given
  (hF : (↑F : Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d N)ᶜ) :
-- imply
  ∃ (m : ℕ) (hNm : N < m) (B : Set (ConfigSpace (Sym2 (boxVerts d m)))), MeasureTheory.cylinder F S = boxRestrict d m ⁻¹' B ∧ DependsOnOutside (ocd_innerEdgeFinset (Vin := boxVerts d N) (boxVertInclLE d (le_of_lt hNm))) B := by
-- proof
  apply StatMech.FK.exteriorCylinder_realise_in_box N F S hF

/--
[isFKDLR_freeMass_mul_exterior_le_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma isFKDLR_freeMass_mul_exterior_le_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N : ℕ}
  {p q : ℝ}
  {phi : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hphi : IsFKDLR d p q phi)
  (hA : IsIncreasing A)
  (hs : @MeasurableSet _ (outsideSigma (fkTailEdgeWindow d N)) s) :
-- imply
  dlrBcEventMass (boxGraph d N) (⊥ : SimpleGraph (boxVerts d N)) p q A * (phi : Measure _).real s ≤ (phi : Measure _).real ((boxRestrict d N ⁻¹' A) ∩ s) := by
-- proof
  apply StatMech.FK.isFKDLR_freeMass_mul_exterior_le_generalQ N hp hp1 hq phi hphi hA hs

/--
[freeInfiniteVolume_tail_box_product_le_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_tail_box_product_le_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
  {N : ℕ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hs : FKIsTailEvent d s)
  (hA : IsIncreasing A) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) * (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real ((boxRestrict d N ⁻¹' A) ∩ s) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_tail_box_product_le_generalQ hp hp1 hq s hs N hA

/--
[freeInfiniteVolume_le_cond_tail_clopen_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_le_cond_tail_clopen_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hs : FKIsTailEvent d s)
  (hs0 : (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
-- imply
  Ising.StochasticallyDominatedClopen (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _))[|s]) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_le_cond_tail_clopen_generalQ hp hp1 hq hs hs0

/--
[freeInfiniteVolume_tail_trivial_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_tail_trivial_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hs : FKIsTailEvent d s) :
-- imply
  (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_tail_trivial_generalQ hp hp1 hq s hs

/--
[freeInfiniteVolume_isErgodic_generalQ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_isErgodic_generalQ_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_isErgodic_generalQ hd hp hp1 hq

/--
[freeInfinite_canonical_uniqueness_all_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfinite_canonical_uniqueness_all_parameters_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) (Percolation.atLeastTwoInfinite d) = 0 ∧ (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _) {omega | Percolation.numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.freeInfinite_canonical_uniqueness_all_parameters hd hp hp1 hq

/--
[freeInfiniteVolume_tail_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_tail_trivial_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p : ℝ}
  {s : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hs : FKIsTailEvent d s) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) s = 0 ∨ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) s = 1 := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_tail_trivial hp hp1 s hs

/--
[freeInfiniteVolume_isErgodic_all_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfiniteVolume_isErgodic_all_parameters_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  StatMech.ConfigSpace.IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_isErgodic_all_parameters hd hp hp1

/--
[freeInfinite_q2_canonical_uniqueness_all_parameters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailTriviality.lean)
-/
@[path]
private lemma freeInfinite_q2_canonical_uniqueness_all_parameters_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p : ℝ}
-- given
  (hd : 1 ≤ d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  ((freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 0} = 1 ∨ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | Percolation.numInfiniteClusters d omega = 1} = 1) ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) (Percolation.atLeastTwoInfinite d) = 0 ∧ (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _) {omega | Percolation.numInfiniteClusters d omega ≤ 1} = 1 := by
-- proof
  apply StatMech.FK.freeInfinite_q2_canonical_uniqueness_all_parameters hd hp hp1


-- created on 2026-10-23

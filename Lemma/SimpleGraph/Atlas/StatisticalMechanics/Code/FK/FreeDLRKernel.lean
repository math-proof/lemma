import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FreeDLRKernel.Part2
open MeasureTheory Set SimpleGraph Filter Topology StatMech StatMech.FK


/--
[freeNestedWiringWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedWiringWeight_nonneg_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {C : SimpleGraph Vin}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ freeNestedWiringWeight Gout ιV p q C := by
-- proof
  apply StatMech.FK.freeNestedWiringWeight_nonneg Gout ιV hp hp1 hq C

/--
[freeNestedWiringWeight_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedWiringWeight_sum_eq_one_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
-- given
  (hι : Function.Injective ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  ∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C = 1 := by
-- proof
  apply StatMech.FK.freeNestedWiringWeight_sum_eq_one Gout ιV hι hp hp1 hq

/--
[freeNestedWiringMeasure_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedWiringMeasure_real_singleton_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {C : SimpleGraph Vin}
-- given
  (hι : Function.Injective ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (freeNestedWiringMeasure Gout ιV hι hp hp1 hq : Measure _).real {C} = freeNestedWiringWeight Gout ιV p q C := by
-- proof
  apply StatMech.FK.freeNestedWiringMeasure_real_singleton Gout ιV hι hp hp1 hq C

/--
[tendsto_probabilityMeasure_real_of_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma tendsto_probabilityMeasure_real_of_isClopen_eq
  [Fintype Vin]
  [DecidableEq Vin]
  [MeasurableSpace α]
  [TopologicalSpace α]
  [OpensMeasurableSpace α]
  [HasOuterApproxClosed α]
  {L : Filter ι}
  {μ : ProbabilityMeasure α}
  {μs : ι → ProbabilityMeasure α}
  {A : Set α}
-- given
  (hμ : Tendsto μs L (𝓝 μ))
  (hA : IsClopen A) :
-- imply
  Tendsto (fun i => (μs i : Measure α).real A) L (𝓝 ((μ : Measure α).real A)) := by
-- proof
  apply StatMech.FK.tendsto_probabilityMeasure_real_of_isClopen hμ hA

/--
[freeNestedMarginal_eq_wiringMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedMarginal_eq_wiringMixture_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {Gin : SimpleGraph Vin}
  [DecidableRel Gin.Adj]
  {Gout : SimpleGraph Vout}
  [DecidableRel Gout.Adj]
  {ιV : Vin → Vout}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 Vin))}
-- given
  (hι : Function.Injective ιV)
  (hadjm : ocd_AdjMatch Gin Gout ιV)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  by classical exact (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1 : ℝ)) ρ * fkProb Gout p q ρ) = ∑ C : SimpleGraph Vin, freeNestedWiringWeight Gout ιV p q C * dlrBcEventMass Gin C p q A := by
-- proof
  apply StatMech.FK.freeNestedMarginal_eq_wiringMixture Gin Gout ιV hι hadjm hp hp1 hq A

/--
[freeNestedInducedWiring_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedInducedWiring_le_boundary_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d m))}
-- given
  (hN : 1 ≤ N)
  (hNm : N < m) :
-- imply
  ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) (bdp_noBdry (Vout := boxVerts d m)) ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
-- proof
  apply StatMech.FK.freeNestedInducedWiring_le_boundary hN hNm ψ

/--
[freeNestedInducedWiring_le_boundary_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedInducedWiring_le_boundary_all_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {ψ : ConfigSpace (Sym2 (boxVerts d m))}
-- given
  (hNm : N < m) :
-- imply
  ocd_inducedWiring (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) (bdp_noBdry (Vout := boxVerts d m)) ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
-- proof
  apply StatMech.FK.freeNestedInducedWiring_le_boundary_all hNm ψ

/--
[freeNestedWiringWeight_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedWiringWeight_support_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {C : SimpleGraph (boxVerts d N)}
-- given
  (hN : 1 ≤ N)
  (hNm : N < m)
  (hC : freeNestedWiringWeight (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) p q C ≠ 0) :
-- imply
  C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
-- proof
  apply StatMech.FK.freeNestedWiringWeight_support hN hNm C hC

/--
[freeNestedWiringWeight_support_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeNestedWiringWeight_support_all_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {C : SimpleGraph (boxVerts d N)}
-- given
  (hNm : N < m)
  (hC : freeNestedWiringWeight (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) p q C ≠ 0) :
-- imply
  C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N) := by
-- proof
  apply StatMech.FK.freeNestedWiringWeight_support_all hNm C hC

/--
[freeFiniteBox_marginal_eq_wiringMixture](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeFiniteBox_marginal_eq_wiringMixture_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  by classical exact (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) = ∑ C : SimpleGraph (boxVerts d N), freeNestedWiringWeight (boxGraph d m) (boxVertInclLE d (le_of_lt hNm)) p q C * dlrBcEventMass (boxGraph d N) C p q A := by
-- proof
  apply StatMech.FK.freeFiniteBox_marginal_eq_wiringMixture hNm hp hp1 hq A

/--
[freeFiniteBox_marginal_specification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeFiniteBox_marginal_specification_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {N m : ℕ}
  {p q : ℝ}
-- given
  (hNm : N < m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  by classical exact ∃ weight : SimpleGraph (boxVerts d N) → ℝ, (∀ C, 0 ≤ weight C) ∧ (∑ C, weight C = 1) ∧ (∀ C, weight C ≠ 0 → C ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d N)) ∧ ∀ A : Set (ConfigSpace (Sym2 (boxVerts d N))), (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) = ∑ C, weight C * dlrBcEventMass (boxGraph d N) C p q A := by
-- proof
  apply StatMech.FK.freeFiniteBox_marginal_specification hNm hp hp1 hq

/--
[freeInfiniteVolume_isFKDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeDLRKernel.lean)
-/
@[path]
private lemma freeInfiniteVolume_isFKDLR_eq
  [Fintype Vin]
  [DecidableEq Vin]
  {d : ℕ}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  IsFKDLR d p q (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq)) := by
-- proof
  apply StatMech.FK.freeInfiniteVolume_isFKDLR hp hp1 hq


-- created on 2026-10-23

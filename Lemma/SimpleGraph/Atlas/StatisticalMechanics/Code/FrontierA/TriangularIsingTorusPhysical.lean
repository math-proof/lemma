import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical
open MeasureTheory StatMech StatMech.FrontierA


/--
[triangular_spinPhase_spaceRoot_mul_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangular_spinPhase_spaceRoot_mul_cos_eq
  {L m n : Nat}
  [NeZero L]
  {a b : Fin 2} :
-- imply
  (ons_spinPhase L a * ons_spaceRoot L ^ m) * (ons_spinPhase L b * ons_spaceRoot L ^ n) + ((ons_spinPhase L a * ons_spaceRoot L ^ m) * (ons_spinPhase L b * ons_spaceRoot L ^ n))⁻¹ = 2 * (Real.cos (2 * Real.pi * ((m + (a.val : Real) / 2) + (n + (b.val : Real) / 2)) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangular_spinPhase_spaceRoot_mul_cos L m n a b

/--
[triangularTorus_sector_tanh_sq_eq_highTempProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorus_sector_tanh_sq_eq_highTempProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ^ 2 = ∏ j : ZMod L × ZMod L, (triangularIsingHighTempSymbol J1 J2 J3 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_sector_tanh_sq_eq_highTempProduct L J1 J2 J3 rho a b hrho

/--
[triangularTorus_normalizedSector_sq_eq_symbolProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorus_normalizedSector_sq_eq_symbolProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I) :
-- imply
  (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) * triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b) ^ 2 = ∏ j : ZMod L × ZMod L, (triangularIsingSymbol J1 J2 J3 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_normalizedSector_sq_eq_symbolProduct L J1 J2 J3 rho a b hrho

/--
[triangularTorus_normalizedSector_log_norm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorus_normalizedSector_log_norm_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Real.log ‖ (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) : Complex) * triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b‖ = (1 / 2 : Real) * ∑ j : ZMod L × ZMod L, Real.log (triangularIsingSymbol J1 J2 J3 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_normalizedSector_log_norm_eq L J1 J2 J3 rho a b hrho hpos

/--
[triangularTorus_normalizedSector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorus_normalizedSector_ne_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  (((Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) : Real) : Complex) * triangularTorusWeightedSpinCharacterSum L (triangularTorusEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) a b ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_normalizedSector_ne_zero L J1 J2 J3 rho a b hrho hpos

/--
[triangularIsingSymbol_riemann_tendsto_spinShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularIsingSymbol_riemann_tendsto_spinShift_eq
  {J1 J2 J3 : Real}
  {a b : Fin 2}
-- given
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun L : Nat => (2 * Real.pi / L) ^ 2 * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, Real.log (triangularIsingSymbol J1 J2 J3 (2 * Real.pi * (i + (a.val : Real) / 2) / L) (2 * Real.pi * (j + (b.val : Real) / 2) / L))) Filter.atTop (nhds (∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularIsingSymbol_riemann_tendsto_spinShift J1 J2 J3 a b hpos

/--
[triangularTorusRealEdgeWeight_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusRealEdgeWeight_cast_eq
  {L : Nat}
  {t1 t2 t3 : Real}
  {edge : Sym2 (ZMod L × ZMod L)} :
-- imply
  (triangularTorusRealEdgeWeight L t1 t2 t3 edge : Complex) = triangularTorusEdgeWeight L t1 t2 t3 edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusRealEdgeWeight_cast L t1 t2 t3 edge

/--
[triangularTorusNormalizedEvenSubgraph_log_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedEvenSubgraph_log_sandwich_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hJ1 : 0 ≤ J1)
  (hJ2 : 0 ≤ J2)
  (hJ3 : 0 ≤ J3) :
-- imply
  let C := (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) let weight := triangularTorusRealEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3) let sector : Fin 2 -> Fin 2 -> Complex := fun a b => (C : Complex) * triangularTorusWeightedSpinCharacterSum L (fun edge => (weight edge : Complex)) a b Real.log (arfSectorNormMax sector) ≤ Real.log (C * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ∧ Real.log (C * inhomogeneousEvenSubgraphSum (triangularTorusGraph L) weight) ≤ Real.log (arfSectorNormMax sector) + Real.log 2 := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedEvenSubgraph_log_sandwich L J1 J2 J3 rho hJ1 hJ2 hJ3

/--
[triangularTorusNormalizedSector_logDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedSector_logDensity_tendsto_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
  {a b : Fin 2}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => Real.log ‖triangularTorusNormalizedSectorSequence J1 J2 J3 rho a b n‖ / (n + 3 : Real) ^ 2) Filter.atTop (nhds ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedSector_logDensity_tendsto J1 J2 J3 rho a b hrho hpos

/--
[triangularTorusNormalizedSectorMax_logDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedSectorMax_logDensity_tendsto_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedSectorMax_logDensity_tendsto J1 J2 J3 rho hrho hpos

/--
[triangularTorusEdgeWeight_real_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusEdgeWeight_real_cast_eq
  {L : Nat}
  {x y z : Real} :
-- imply
  (fun edge => (triangularTorusRealEdgeWeight L x y z edge : Complex)) = triangularTorusEdgeWeight L x y z := by
-- proof
  apply StatMech.FrontierA.triangularTorusEdgeWeight_real_cast L x y z

/--
[triangularTorusRealEdgeWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusRealEdgeWeight_nonneg_eq
  {L : Nat}
  {x y z : Real}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y)
  (hz : 0 ≤ z) :
-- imply
  ∀ edge, 0 ≤ triangularTorusRealEdgeWeight L x y z edge := by
-- proof
  apply StatMech.FrontierA.triangularTorusRealEdgeWeight_nonneg L hx hy hz

/--
[arfSectorNormMax_nonneg_real_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma arfSectorNormMax_nonneg_real_mul_eq
  {c : Real}
  {sector : Fin 2 → Fin 2 → Complex}
-- given
  (hc : 0 ≤ c) :
-- imply
  arfSectorNormMax (fun a b => (c : Complex) * sector a b) = c * arfSectorNormMax sector := by
-- proof
  apply StatMech.FrontierA.arfSectorNormMax_nonneg_real_mul c hc sector

/--
[triangularTorusNormalizedSectorMaxSequence_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedSectorMaxSequence_eq_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
  {n : Nat} :
-- imply
  triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n = (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ ((n + 3) * (n + 3)) * arfSectorNormMax (triangularTorusSectorSequence (fun L => triangularTorusRealEdgeWeight L (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) n) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedSectorMaxSequence_eq J1 J2 J3 rho n

/--
[triangularTorusNormalizedEven_log_gap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedEven_log_gap_tendsto_zero_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hJ1 : 0 ≤ J1)
  (hJ2 : 0 ≤ J2)
  (hJ3 : 0 ≤ J3) :
-- imply
  Filter.Tendsto (fun n : Nat => (Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) - Real.log (triangularTorusNormalizedSectorMaxSequence J1 J2 J3 rho n)) / (n + 3 : Real) ^ 2) Filter.atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedEven_log_gap_tendsto_zero J1 J2 J3 rho hJ1 hJ2 hJ3

/--
[triangularTorusNormalizedEven_logDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusNormalizedEven_logDensity_tendsto_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hJ1 : 0 ≤ J1)
  (hJ2 : 0 ≤ J2)
  (hJ3 : 0 ≤ J3)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => Real.log (triangularTorusNormalizedEvenSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds ((1 / (8 * Real.pi ^ 2)) * ∫ k1 in (-Real.pi)..Real.pi, ∫ k2 in (-Real.pi)..Real.pi, Real.log (triangularIsingSymbol J1 J2 J3 k1 k2))) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNormalizedEven_logDensity_tendsto J1 J2 J3 rho hrho hJ1 hJ2 hJ3 hpos

/--
[prod_triangularPositiveEdgeSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma prod_triangularPositiveEdgeSources_eq
  [CommMonoid A]
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {f : Sym2 (ZMod L × ZMod L) → A}
-- given
  (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
-- imply
  (∏ edge ∈ F, f edge) = ∏ a : Fin 3, ∏ p ∈ triangularPositiveEdgeSources L F a, f (triangularPositiveEdge L a p) := by
-- proof
  apply StatMech.FrontierA.prod_triangularPositiveEdgeSources L F hF f

/--
[triangularPositiveEdgeSources_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularPositiveEdgeSources_edgeFinset_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 3} :
-- imply
  triangularPositiveEdgeSources L (triangularTorusGraph L).edgeFinset a = Finset.univ := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdgeSources_edgeFinset L a

/--
[triangularTorusRealEdgeWeight_positiveEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusRealEdgeWeight_positiveEdge_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real}
  {a : Fin 3}
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusRealEdgeWeight L J1 J2 J3 (triangularPositiveEdge L a p) = ![J1, J2, J3] a := by
-- proof
  apply StatMech.FrontierA.triangularTorusRealEdgeWeight_positiveEdge L J1 J2 J3 a p

/--
[prod_cosh_triangularTorusRealEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma prod_cosh_triangularTorusRealEdgeWeight_eq
  {L : Nat}
  [Fact (2 < L)]
  {J1 J2 J3 : Real} :
-- imply
  (∏ edge ∈ (triangularTorusGraph L).edgeFinset, Real.cosh (triangularTorusRealEdgeWeight L J1 J2 J3 edge)) = (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) := by
-- proof
  apply StatMech.FrontierA.prod_cosh_triangularTorusRealEdgeWeight L J1 J2 J3

/--
[triangularTorusIsingPartitionSequence_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartitionSequence_eq_eq
  {J1 J2 J3 : Real}
  {n : Nat} :
-- imply
  triangularTorusIsingPartitionSequence J1 J2 J3 n = 2 ^ ((n + 3) * (n + 3)) * triangularTorusNormalizedEvenSequence J1 J2 J3 n := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartitionSequence_eq J1 J2 J3 n

/--
[triangularTorusIsingPartition_freeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPhysical.lean)
-/
@[path]
private lemma triangularTorusIsingPartition_freeEnergy_tendsto_eq
  {J1 J2 J3 : Real}
  {rho : Complex}
-- given
  (hrho : rho ^ 4 = Complex.I)
  (hJ1 : 0 ≤ J1)
  (hJ2 : 0 ≤ J2)
  (hJ3 : 0 ≤ J3)
  (hpos : forall k1 k2, 0 < triangularIsingSymbol J1 J2 J3 k1 k2) :
-- imply
  Filter.Tendsto (fun n : Nat => -Real.log (triangularTorusIsingPartitionSequence J1 J2 J3 n) / (n + 3 : Real) ^ 2) Filter.atTop (nhds (triangularIsingFreeEnergyValue J1 J2 J3)) := by
-- proof
  apply StatMech.FrontierA.triangularTorusIsingPartition_freeEnergy_tendsto J1 J2 J3 rho hrho hJ1 hJ2 hJ3 hpos


-- created on 2026-10-23

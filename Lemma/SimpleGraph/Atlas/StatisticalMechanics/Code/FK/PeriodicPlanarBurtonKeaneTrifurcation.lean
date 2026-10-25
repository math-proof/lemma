import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
open Filter MeasureTheory Set SimpleGraph Topology Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[measurable_removeVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma measurable_removeVertex_eq
  [Countable V]
  [DecidableEq V]
  {x : V} :
-- imply
  Measurable (removeVertex x : ConfigSpace (Sym2 V) -> ConfigSpace (Sym2 V)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.measurable_removeVertex x

/--
[PeriodicGraph.removeVertex_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma removeVertex_configTranslate_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  removeVertex (P.shift z x) (P.configTranslate z omega) = P.configTranslate z (removeVertex x omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.removeVertex_configTranslate P z omega x

/--
[PeriodicGraph.measurableSet_openAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma measurableSet_openAdj_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x y : V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_openAdj P x y

/--
[PeriodicGraph.measurableSet_isTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma measurableSet_isTrifurcation_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x : V} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 V) | P.IsTrifurcation omega x} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.measurableSet_isTrifurcation P x

/--
[PeriodicGraph.isTrifurcation_configTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma isTrifurcation_configTranslate_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {omega : ConfigSpace (Sym2 V)}
  {x : V} :
-- imply
  P.IsTrifurcation (P.configTranslate z omega) (P.shift z x) ↔ P.IsTrifurcation omega x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.isTrifurcation_configTranslate P z omega x

/--
[PeriodicGraph.trifurcation_measure_eq_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma trifurcation_measure_eq_orbit_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {u : V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu {omega | P.IsTrifurcation omega (P.shift z u)} = mu {omega | P.IsTrifurcation omega u} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.trifurcation_measure_eq_orbit P mu hTI z u

/--
[PeriodicGraph.fundamentalDomain_mem_orbitBox_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma fundamentalDomain_mem_orbitBox_zero_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {u : V}
-- given
  (hu : u ∈ P.fundamentalDomain) :
-- imply
  u ∈ P.orbitBox 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fundamentalDomain_mem_orbitBox_zero P hu

/--
[PeriodicGraph.neighbor_mem_orbitBox_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma neighbor_mem_orbitBox_add_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n : Nat}
  {x y : V}
-- given
  (hx : x ∈ P.orbitBox n)
  (hxy : P.graph.Adj x y) :
-- imply
  y ∈ P.orbitBox (n + P.neighborOrbitRadius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.neighbor_mem_orbitBox_add P hx hxy

/--
[PeriodicGraph.orbitShell_subset_source_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitShell_subset_source_image_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n c : Nat} :
-- imply
  P.orbitShell n c ⊆ (P.orbitShellSource n c).image (fun zu => P.shift zu.1 zu.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitShell_subset_source_image P n c

/--
[PeriodicGraph.orbitShell_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitShell_card_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {n c : Nat} :
-- imply
  (P.orbitShell n c).card <= (((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) * P.fundamentalDomain.card) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitShell_card_le P n c

/--
[PeriodicPlaneEmbedding.orbitBox_card_ge_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitBox_card_ge_quadratic_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {n : Nat} :
-- imply
  (2 * n + 1) ^ 2 <= (P.orbitBox n).card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitBox_card_ge_quadratic E n

/--
[removeVertex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma removeVertex_le_eq
  [Countable V]
  [DecidableEq V]
  {x : V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  removeVertex x omega <= omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.removeVertex_le x omega

/--
[PeriodicGraph.openSubgraph_removeVertex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma openSubgraph_removeVertex_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {x : V}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  P.openSubgraph (removeVertex x omega) <= P.openSubgraph omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.openSubgraph_removeVertex_le P x omega

/--
[PeriodicGraph.trifurcation_orbitShell_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma trifurcation_orbitShell_witnesses_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {n : Nat}
  {x : V}
-- given
  (hx : x ∈ P.orbitBox n)
  (htrif : P.IsTrifurcation omega x) :
-- imply
  ∃ t1 t2 t3 : V, t1 ∈ P.orbitShell n P.neighborOrbitRadius ∧ t2 ∈ P.orbitShell n P.neighborOrbitRadius ∧ t3 ∈ P.orbitShell n P.neighborOrbitRadius ∧ x ≠ t1 ∧ x ≠ t2 ∧ x ≠ t3 ∧ (P.openSubgraph omega).Reachable x t1 ∧ (P.openSubgraph omega).Reachable x t2 ∧ (P.openSubgraph omega).Reachable x t3 ∧ ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t2 ∧ ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t1 t3 ∧ ¬ ((P.openSubgraph omega).deleteIncidenceSet x).Reachable t2 t3 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.trifurcation_orbitShell_witnesses P omega n hx htrif

/--
[PeriodicPlaneEmbedding.orbitTrifurcationHubs_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitTrifurcationHubs_card_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {u : V}
  {omega : ConfigSpace (Sym2 V)}
  {n : Nat} :
-- imply
  (P.orbitTrifurcationHubs u omega n).card = (P.orbitTrifurcationCoords u omega n).card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitTrifurcationHubs_card E u omega n

/--
[PeriodicPlaneEmbedding.orbitTrifurcation_count_le_shell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitTrifurcation_count_le_shell_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {u : V}
  {omega : ConfigSpace (Sym2 V)}
  {n : Nat}
-- given
  (hu : u ∈ P.fundamentalDomain) :
-- imply
  (P.orbitTrifurcationCoords u omega n).card <= (P.orbitShell n P.neighborOrbitRadius).card := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitTrifurcation_count_le_shell E u hu omega n

/--
[PeriodicGraph.orbitTrifurcationCoords_cast_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitTrifurcationCoords_cast_eq_sum_indicator_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {u : V}
  {omega : ConfigSpace (Sym2 V)}
  {n : Nat} :
-- imply
  ((P.orbitTrifurcationCoords u omega n).card : ENNReal) = ∑ z ∈ (box_finite 2 n).toFinset, ({eta | P.IsTrifurcation eta (P.shift z u)}.indicator (fun _ => (1 : ENNReal))) omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitTrifurcationCoords_cast_eq_sum_indicator P u omega n

/--
[PeriodicGraph.expected_orbitTrifurcationCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma expected_orbitTrifurcationCoords_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {u : V}
  {n : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  ∫⁻ omega, ((P.orbitTrifurcationCoords u omega n).card : ENNReal) ∂mu = ((box_finite 2 n).toFinset.card) • mu {omega | P.IsTrifurcation omega u} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.expected_orbitTrifurcationCoords P mu hTI u n

/--
[PeriodicGraph.orbitShell_polynomial_ratio_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma orbitShell_polynomial_ratio_tendsto_zero_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {c : Nat} :
-- imply
  Tendsto (fun n => ((((2 * (n + c) + 1) ^ 2 - (2 * n + 1) ^ 2) * P.fundamentalDomain.card : Nat) : Real) / (((2 * n + 1) ^ 2 : Nat) : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.orbitShell_polynomial_ratio_tendsto_zero P c

/--
[PeriodicPlaneEmbedding.trifurcation_measure_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean)
-/
@[path]
private lemma trifurcation_measure_eq_zero_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {u : V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hu : u ∈ P.fundamentalDomain) :
-- imply
  mu {omega | P.IsTrifurcation omega u} = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.trifurcation_measure_eq_zero E mu hTI u hu


-- created on 2026-10-23

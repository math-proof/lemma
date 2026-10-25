import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneEscape.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.mem_connectedWithinSet_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma mem_connectedWithinSet_of_walk_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Set V}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hp : ∀ v ∈ p.support, v ∈ A) :
-- imply
  omega ∈ P.connectedWithinSet A x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_connectedWithinSet_of_walk P p hp

/--
[PeriodicPlaneEmbedding.exists_boundary_walk_of_walk_to_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_boundary_walk_of_walk_to_left_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r : ℝ}
  {x y : V}
  {p : (P.openSubgraph omega).Walk x y}
-- given
  (hx : x ∈ E.rightHalfPlaneVertices r)
  (hy : y ∉ E.rightHalfPlaneVertices r) :
-- imply
  ∃ b ∈ E.rightHalfPlaneBoundaryVertices r, ∃ q : (P.openSubgraph omega).Walk x b, ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_boundary_walk_of_walk_to_left E omega r p hx hy

/--
[PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_boundary_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma connectedWithin_rightHalfPlane_boundary_of_reachable_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r : ℝ}
  {x y : V}
-- given
  (hx : x ∈ E.rightHalfPlaneVertices r)
  (hy : y ∉ E.rightHalfPlaneVertices r)
  (hxy : y ∈ P.cluster omega x) :
-- imply
  ∃ b ∈ E.rightHalfPlaneBoundaryVertices r, omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.connectedWithin_rightHalfPlane_boundary_of_reachable E omega r hx hy hxy

/--
[PeriodicGraph.setHitsInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma setHitsInfinite_measurableSet_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V} :
-- imply
  MeasurableSet (P.setHitsInfinite S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfinite_measurableSet P S

/--
[PeriodicGraph.setHitsInfinite_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma setHitsInfinite_isIncreasing_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Set V} :
-- imply
  IsIncreasing (P.setHitsInfinite S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfinite_isIncreasing P S

/--
[PeriodicGraph.setHitsInfinite_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma setHitsInfinite_translate_preimage_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {z : Site 2}
  {S : Set V} :
-- imply
  P.configTranslate z ⁻¹' P.setHitsInfinite (P.shift z '' S) = P.setHitsInfinite S := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfinite_translate_preimage P z S

/--
[PeriodicGraph.setHitsInfinite_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma setHitsInfinite_translate_measureReal_eq_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {z : Site 2}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (P.setHitsInfinite (P.shift z '' S)) = mu.real (P.setHitsInfinite S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfinite_translate_measureReal_eq P mu hTI z S

/--
[PeriodicGraph.setHitsInfinite_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma setHitsInfinite_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {N : ℕ} :
-- imply
  P.setHitsInfinite (P.orbitBox N : Set V) = P.orbitBoxHitsInfinite N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.setHitsInfinite_orbitBox P N

/--
[PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_leftComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_shift_orbitBox_subset_leftComplement_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ} :
-- imply
  ∃ z : Site 2, ∀ v ∈ P.orbitBox N, P.shift z v ∉ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_shift_orbitBox_subset_leftComplement E N r

/--
[PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_opposite_translated_orbitBox_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {N : ℕ}
  {r : ℝ} :
-- imply
  ∃ z₀ z₁ : Site 2, P.shift z₀ '' (P.orbitBox N : Set V) ⊆ E.rightHalfPlaneVertices r ∧ P.shift z₁ '' (P.shift z₀ '' (P.orbitBox N : Set V)) ⊆ (E.rightHalfPlaneVertices r)ᶜ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_opposite_translated_orbitBox E N r

/--
[PeriodicPlaneEmbedding.unique_two_sides_subset_boundaryConnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma unique_two_sides_subset_boundaryConnection_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {r : ℝ}
  {S T : Set V}
-- given
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩ (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆ P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.unique_two_sides_subset_boundaryConnection E r hS hT

/--
[PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma boundaryConnection_measureReal_ge_mul_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {S T : Set V}
-- given
  (hFKG : IsFKG mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤ mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_mul E mu hFKG hunique r hS hT

/--
[PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_sq_of_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma boundaryConnection_measureReal_ge_sq_of_translate_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {S : Set V}
  {z : Site 2}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hS : S ⊆ E.rightHalfPlaneVertices r)
  (hT : P.shift z '' S ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
-- imply
  (mu.real (P.setHitsInfinite S)) ^ 2 ≤ mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.boundaryConnection_measureReal_ge_sq_of_translate E mu hFKG hTI hunique r S z hS hT

/--
[PeriodicPlaneEmbedding.exists_boundaryConnection_ge_orbitBox_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_boundaryConnection_ge_orbitBox_sq_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {N : ℕ}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : Set V, S ⊆ E.rightHalfPlaneVertices r ∧ (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤ mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) S (E.rightHalfPlaneBoundaryVertices r)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_boundaryConnection_ge_orbitBox_sq E mu hFKG hTI hunique r N

/--
[PeriodicPlaneEmbedding.exists_boundaryConnection_sequence_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_boundaryConnection_sequence_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : ℕ → Set V, (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧ Tendsto (fun N => mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N) (E.rightHalfPlaneBoundaryVertices r))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_boundaryConnection_sequence_tendsto_one E mu hFKG hTI hunique r

/--
[PeriodicPlaneEmbedding.exists_boundaryRay_max_sequence_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneEscape.lean)
-/
@[path]
private lemma exists_boundaryRay_max_sequence_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r : ℝ}
  {s : ℕ → ℝ}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ S : ℕ → Set V, (∀ N, S N ⊆ E.rightHalfPlaneVertices r) ∧ Tendsto (fun N => max (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N) (E.lowerBoundaryRayVertices r (s N)))) (mu.real (P.setConnectionWithin (E.rightHalfPlaneVertices r) (S N) (E.upperBoundaryRayVertices r (s N))))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_boundaryRay_max_sequence_tendsto_one E mu hFKG hTI hunique r s


-- created on 2026-10-23

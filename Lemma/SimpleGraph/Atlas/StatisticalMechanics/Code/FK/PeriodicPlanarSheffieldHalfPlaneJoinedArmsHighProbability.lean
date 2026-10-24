import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_nat_abs_bound_on_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_nat_abs_bound_on_finset_eq
  [DecidableEq V]
  [Countable V]
  {S : Finset V}
  {f : V → Real} :
-- imply
  ∃ K : Nat, ∀ x ∈ S, := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_nat_abs_bound_on_finset S f

/--
[PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_margin E mu hFKG hTI hunique hrR hepsilon

/--
[PeriodicPlaneEmbedding.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {s : Real}
  {t : Int}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ U = L.image (P.shift (verticalShift (1 + t))) ∧ 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin E mu hFKG hTI hunique hrR s t hepsilon

/--
[PeriodicPlaneEmbedding.exists_highProbability_ordered_finiteJoinedBoundaryArmEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_highProbability_ordered_finiteJoinedBoundaryArmEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r R : Real}
  {band buffer : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hrR : r ≤ R)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m : Nat, ∃ L U : Finset V, ∃ n : Nat, band + buffer < m ∧ (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧ U = L.image (P.shift (verticalShift (1 + 2 * (m : Int)))) ∧ (∀ x ∈ L, ∀ y ∈ U, E.vertexCoord x 1 + 2 * (band + buffer : Nat) + 2 < E.vertexCoord y 1) ∧ 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r (-(m : Real)) m n L U) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_ordered_finiteJoinedBoundaryArmEvent E mu hFKG hTI hunique hrR band buffer hepsilon

/--
[PeriodicPlaneEmbedding.exists_highProbability_primalHalfPlaneBarrierReady](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_highProbability_primalHalfPlaneBarrierReady_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B : Real}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n L U) ∧ E.finiteJoinedBoundaryArmEvent r 0 1 n L U ⊆ E.primalHalfPlaneBarrierReady := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_primalHalfPlaneBarrierReady E mu hFKG hTI hunique r B hB0 hB hepsilon

/--
[PeriodicPlaneEmbedding.exists_highProbability_separated_primalHalfPlaneBarrierReady](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.lean)
-/
@[path]
private lemma exists_highProbability_separated_primalHalfPlaneBarrierReady_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (ht : 0 < t)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ L U : Finset V, ∃ n : Nat, 1 - epsilon < mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) ∧ E.finiteJoinedBoundaryArmEvent r s (s + t) n L U ⊆ E.primalHalfPlaneBarrierReady := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_highProbability_separated_primalHalfPlaneBarrierReady E mu hFKG hTI hunique r B s t ht hB0 hB hepsilon


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[outerContourFill_of_planarConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma outerContourFill_of_planarConnectivity_eq
  {n : ℕ}
-- given
  (h : PlanarConnectivity n) :
-- imply
  OuterContourFill n := by
-- proof
  apply StatMech.Ising.outerContourFill_of_planarConnectivity n h

/--
[peierls_long_range_order_of_planarConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma peierls_long_range_order_of_planarConnectivity_eq
-- given
  (hConn : ∀ n : ℕ, PlanarConnectivity n) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Ising.peierls_long_range_order_of_planarConnectivity hConn

/--
[twoComponentCount_of_offSupport_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma twoComponentCount_of_offSupport_connected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {p q : Site 2}
-- given
  (hp : ¬ Even (jec_rayCount p Vc))
  (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
  (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
  (hOutOff : ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc → ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Ising.twoComponentCount_of_offSupport_connected Vc hp hq hInOff hOutOff

/--
[walk_of_induce_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma walk_of_induce_walk_eq
  {G : SimpleGraph V}
  {s : Set V}
  {a b : (s : Set V)}
  {pInd : (G.induce s).Walk a b} :
-- imply
  ∃ p : G.Walk (a : V) (b : V), ∀ v ∈ p.support, v ∈ s := by
-- proof
  apply StatMech.Ising.walk_of_induce_walk G s pInd

/--
[singletonOrigin_planarConnectivity_walks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma singletonOrigin_planarConnectivity_walks_eq :
-- imply
  singletonBoundarySupport.Nonempty ∧ (∀ f ∈ singletonBoundarySupport, ∀ g ∈ singletonBoundarySupport, ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk f g, ∀ v ∈ p.support, v ∈ singletonBoundarySupport) := by
-- proof
  apply StatMech.Ising.singletonOrigin_planarConnectivity_walks

/--
[planarConnectivity_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma planarConnectivity_nonvacuous_eq
  {n : ℕ} :
-- imply
  ∃ τ : {x // x ∈ box 2 n} → Bool, glue (plusField 2) τ (origin 2) = false ∧ (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster ({origin 2} : Finset (Site 2)) ∧ ContourEvent (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) τ) ∧ ∃ (T : Finset (Site 2)) (j : ℕ), (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧ T.Nonempty ∧ (∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).Walk f g, ∀ v ∈ p.support, v ∈ T) ∧ j < contourLen (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.planarConnectivity_nonvacuous n

/--
[planarConnectivity_isoOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsPlanarAssembly.lean)
-/
@[path]
private lemma planarConnectivity_isoOrigin_eq
  {n : ℕ} :
-- imply
  glue (plusField 2) (isoOriginCompletion n) (origin 2) = false → ∃ K : Finset (Site 2), (↑K : Set (Site 2)) ⊆ box 2 n ∧ IsConnectedCluster K ∧ ContourEvent (↑K : Set (Site 2)) (bondFinsetTouch 2 n) (glue (plusField 2) (isoOriginCompletion n)) ∧ ∃ (T : Finset (Site 2)) (j : ℕ), (faceBoundaryGraph (↑K : Set (Site 2))).support ⊆ (T : Set (Site 2)) ∧ T.Nonempty ∧ (∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f g, ∀ v ∈ p.support, v ∈ T) ∧ j < contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ∧ axisVertex 2 j ∈ T := by
-- proof
  apply StatMech.Ising.planarConnectivity_isoOrigin n


-- created on 2026-10-23

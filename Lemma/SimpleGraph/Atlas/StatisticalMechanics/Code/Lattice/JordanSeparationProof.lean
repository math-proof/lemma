import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationProof.Part2
open SimpleGraph Function Set StatMech StatMech.Lattice


/--
[jsp_odd_propagates_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_odd_propagates_off_support_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {i : ℕ}
  {z₀ : Site 2}
  {p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀}
-- given
  (hK : K.Finite)
  (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
  (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  ¬ Even (jec_rayCount ((dartNext K)^[i] a.1).tail (olb_orbitLoop K hK a.1 a.2)) := by
-- proof
  apply StatMech.Lattice.jsp_odd_propagates_off_support K hK a i p hp hodd

/--
[jsp_tailOdd_of_oddCell_reaches_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_tailOdd_of_oddCell_reaches_tail_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z₀ : Site 2}
  {i : ℕ}
  {p : (hypercubicLattice 2).Walk ((dartNext K)^[i] a.1).tail z₀}
-- given
  (hK : K.Finite)
  (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK a.1 a.2).support)
  (hodd : ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  wwit_TailOdd K hK a := by
-- proof
  apply StatMech.Lattice.jsp_tailOdd_of_oddCell_reaches_tail K hK a i p hp hodd

/--
[jsp_tailOdd_of_orbitWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_tailOdd_of_orbitWinds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hwind : jsp_OrbitWinds K hK a) :
-- imply
  wwit_TailOdd K hK a := by
-- proof
  apply StatMech.Lattice.jsp_tailOdd_of_orbitWinds K hK a hwind

/--
[jsp_winding_witness_of_orbitWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_winding_witness_of_orbitWinds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hwind : jsp_OrbitWinds K hK a) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := by
-- proof
  apply StatMech.Lattice.jsp_winding_witness_of_orbitWinds K hK a hwind

/--
[jsp_starHull_tailOdd_of_orbitWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_starHull_tailOdd_of_orbitWinds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hwind : jsp_OrbitWinds (ndt_StarHull K) hSK a) :
-- imply
  wwit_TailOdd (ndt_StarHull K) hSK a := by
-- proof
  apply StatMech.Lattice.jsp_starHull_tailOdd_of_orbitWinds K hSK a hwind

/--
[jsp_starHull_winding_witness_of_orbitWinds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_starHull_winding_witness_of_orbitWinds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hwind : jsp_OrbitWinds (ndt_StarHull K) hSK a) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ ndt_StarHull K ∧ ¬ Even (jec_rayCount z₀ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)) := by
-- proof
  apply StatMech.Lattice.jsp_starHull_winding_witness_of_orbitWinds K hSK a hwind

/--
[jsp_two_component_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_two_component_separation_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {p q : Site 2}
-- given
  (hK : K.Finite)
  (hp : ¬ Even (jec_rayCount p (olb_orbitLoop K hK a.1 a.2)))
  (hq : ∀ w ∈ (olb_orbitLoop K hK a.1 a.2).support, w 0 ≤ q 0 - 1)
  (hin : ∀ s t : Site 2, s ∈ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) → t ∈ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) → (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).Reachable s t)
  (hout : ∀ s t : Site 2, s ∉ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) → t ∉ jec_leftRegion (olb_orbitLoop K hK a.1 a.2) → (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).Reachable s t) :
-- imply
  Nat.card (latticeMinusBarrier (jec_leftRegion (olb_orbitLoop K hK a.1 a.2))).ConnectedComponent = 2 := by
-- proof
  apply StatMech.Lattice.jsp_two_component_separation K hK a hp hq hin hout

/--
[jsp_orbitWinds_oddRay_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationProof.lean)
-/
@[path]
private lemma jsp_orbitWinds_oddRay_satisfiable_eq :
-- imply
  ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) := by
-- proof
  apply StatMech.Lattice.jsp_orbitWinds_oddRay_satisfiable


-- created on 2026-10-23

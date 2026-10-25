import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[wwit_singleVisit_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_singleVisit_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
  {i : ℕ}
-- given
  (h : usc_visitSet K a f = {i}) :
-- imply
  usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
-- proof
  apply StatMech.Lattice.wwit_singleVisit_localTurn_mem K a f i h

/--
[wwit_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (hmult : usc_FaceMultiplicityOne K a) :
-- imply
  usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
-- proof
  apply StatMech.Lattice.wwit_localTurn_mem K a hmult f

/--
[wwit_localTurn_mem_orbitFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_localTurn_mem_orbitFaces_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (hmult : usc_FaceMultiplicityOne K a)
  (_hf : f ∈ usc_orbitFaces K a) :
-- imply
  usc_localTurn K a f = 1 ∨ usc_localTurn K a f = 0 ∨ usc_localTurn K a f = -1 := by
-- proof
  apply StatMech.Lattice.wwit_localTurn_mem_orbitFaces K a hmult f _hf

/--
[wwit_localTurn_sum_eq_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_localTurn_sum_eq_totalTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f = totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.wwit_localTurn_sum_eq_totalTurn K a

/--
[wwit_exists_pos_of_sum_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_exists_pos_of_sum_eq_four_eq
  {s : Finset (Site 2)}
  {g : Site 2 → ℤ}
-- given
  (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
  (hsum : ∑ f ∈ s, g f = 4) :
-- imply
  ∃ f ∈ s, g f = 1 := by
-- proof
  apply StatMech.Lattice.wwit_exists_pos_of_sum_eq_four g hg hsum

/--
[wwit_exists_neg_of_sum_eq_negFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_exists_neg_of_sum_eq_negFour_eq
  {s : Finset (Site 2)}
  {g : Site 2 → ℤ}
-- given
  (hg : ∀ f ∈ s, g f = 1 ∨ g f = 0 ∨ g f = -1)
  (hsum : ∑ f ∈ s, g f = -4) :
-- imply
  ∃ f ∈ s, g f = -1 := by
-- proof
  apply StatMech.Lattice.wwit_exists_neg_of_sum_eq_negFour g hg hsum

/--
[wwit_exists_convex_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_exists_convex_corner_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmult : usc_FaceMultiplicityOne K a)
  (hturn : TurningIsFullRevolution K a) :
-- imply
  (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = 1) ∨ (∃ f ∈ usc_orbitFaces K a, usc_localTurn K a f = -1) := by
-- proof
  apply StatMech.Lattice.wwit_exists_convex_corner K a hmult hturn

/--
[wwit_starHull_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_starHull_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {f : Site 2} :
-- imply
  usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨ usc_localTurn (ndt_StarHull K) a f = -1 := by
-- proof
  apply StatMech.Lattice.wwit_starHull_localTurn_mem K a f

/--
[wwit_starHull_exists_convex_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_starHull_exists_convex_corner_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hturn : TurningIsFullRevolution (ndt_StarHull K) a) :
-- imply
  (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = 1) ∨ (∃ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f = -1) := by
-- proof
  apply StatMech.Lattice.wwit_starHull_exists_convex_corner K a hturn

/--
[wwit_dart_of_localTurn_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_dart_of_localTurn_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {f : Site 2}
-- given
  (hmult : usc_FaceMultiplicityOne K a)
  (hf1 : usc_localTurn K a f = 1) :
-- imply
  ∃ i : ℕ, i ∈ usc_visitSet K a f ∧ dartFace ((dartNext K)^[i] a.1) = f ∧ turnZ K ((dartNext K)^[i] a.1) = 1 := by
-- proof
  apply StatMech.Lattice.wwit_dart_of_localTurn_one K a hmult f hf1

/--
[wwit_cornerCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_cornerCell_mem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hturn : turnZ K e = 1) :
-- imply
  e.head + (-rot90Fun e.dir) ∈ K := by
-- proof
  apply StatMech.Lattice.wwit_cornerCell_mem K e hturn

/--
[wwit_cornerCell_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_cornerCell_def_eq
  {e : Dart} :
-- imply
  wwit_cornerCell e = e.head + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Lattice.wwit_cornerCell_def e

/--
[wwit_orbit_tail_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_orbit_tail_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {i : ℕ} :
-- imply
  ((dartNext K)^[i] a.1).tail ∈ K := by
-- proof
  apply StatMech.Lattice.wwit_orbit_tail_mem K a i

/--
[wwit_winding_witness_of_tailOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_winding_witness_of_tailOdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hprim : wwit_TailOdd K hK a) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (olb_orbitLoop K hK a.1 a.2)) := by
-- proof
  apply StatMech.Lattice.wwit_winding_witness_of_tailOdd K hK a hprim

/--
[wwit_starHull_winding_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_starHull_winding_witness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hprim : wwit_TailOdd (ndt_StarHull K) hSK a) :
-- imply
  ∃ z₀ : Site 2, z₀ ∈ ndt_StarHull K ∧ ¬ Even (jec_rayCount z₀ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)) := by
-- proof
  apply StatMech.Lattice.wwit_starHull_winding_witness K hSK a hprim

/--
[wwit_starHull_bdEdgeMatch_of_tailOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_starHull_bdEdgeMatch_of_tailOdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {i : ℕ}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hodd : ¬ Even (jec_rayCount ((dartNext (ndt_StarHull K))^[i] a.1).tail (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2)))
  (hExt : ∀ z, z ∉ ndt_StarHull K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support) ∧ (∀ q ∈ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support, z0 0 ≤ q 0))
  (hInt : ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z ((dartNext (ndt_StarHull K))^[i] a.1).tail, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2).support)) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK a.1 a.2) := by
-- proof
  apply StatMech.Lattice.wwit_starHull_bdEdgeMatch_of_tailOdd K hSK a i hodd hExt hInt

/--
[wwit_unitSquareLoop_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean)
-/
@[path]
private lemma wwit_unitSquareLoop_inside_odd_eq :
-- imply
  ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) := by
-- proof
  apply StatMech.Lattice.wwit_unitSquareLoop_inside_odd


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
open MeasureTheory Set SimpleGraph StatMech StatMech.Percolation


/--
[lastIndexMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma lastIndexMem_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {S : Set V}
  [DecidablePred (· ∈ S)]
-- given
  (ha : a ∈ S)
  (hb : b ∉ S) :
-- imply
  ∃ m, m < p.length ∧ p.getVert m ∈ S ∧ ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S := by
-- proof
  apply StatMech.Percolation.lastIndexMem p S ha hb

/--
[drop_avoids_of_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma drop_avoids_of_after_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {S : Set V}
  {m : ℕ}
-- given
  (hm : m < p.length)
  (hafter : ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S) :
-- imply
  ∀ z ∈ (p.drop (m + 1)).support, z ∉ S := by
-- proof
  apply StatMech.Percolation.drop_avoids_of_after p S hm hafter

/--
[exists_lastExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma exists_lastExit_eq
  {G : SimpleGraph V}
  {a b : V}
  {p : G.Walk a b}
  {S : Set V}
  [DecidablePred (· ∈ S)]
-- given
  (ha : a ∈ S)
  (hb : b ∉ S) :
-- imply
  ∃ (x y : V) (_hx : x ∈ S) (hy : y ∉ S) (_hadj : G.Adj x y), Nonempty ((G.induce {v | v ∉ S}).Walk ⟨y, hy⟩ ⟨b, hb⟩) := by
-- proof
  apply StatMech.Percolation.exists_lastExit p S ha hb

/--
[lattice_lastExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma lattice_lastExit_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {K : Set (Site d)}
  {o v : Site d}
-- given
  (ho : o ∈ K)
  (hv : v ∉ K)
  (hconn : Connected d ω o v) :
-- imply
  ∃ (x y : Site d) (_hx : x ∈ K) (hy : y ∉ K), IsOpenEdge d ω x y ∧ ConnectedWithin d ω {z | z ∉ K} ⟨y, hy⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Percolation.lattice_lastExit ω K o v ho hv hconn

/--
[boundaryOpen_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma boundaryOpen_dependsOn_eq
  {d : ℕ}
  {C : Set (Site d)}
  {x y : Site d} :
-- imply
  DependsOn ({ω | boundaryOpen d C x y ω}.indicator (fun _ => (1 : ℝ))) ({s(x, y)} : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.boundaryOpen_dependsOn C x y

/--
[crossingEvent_lastExit_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean)
-/
@[path]
private lemma crossingEvent_lastExit_subset_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {n : ℕ}
-- given
  (hoS : origin d ∈ (S : Set (Site d)))
  (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
-- imply
  crossingEvent d n ⊆ ⋃ (C : Set (Site d)), ⋃ (x : Site d), ⋃ (y : Site d), (clusterEvent d (S : Set (Site d)) (origin d) C ∩ {ω | boundaryOpen d C x y ω} ∩ {ω | offClusterCrossing d C y n ω}) := by
-- proof
  apply StatMech.Percolation.crossingEvent_lastExit_subset S hoS n hSbox


-- created on 2026-10-23

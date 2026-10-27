import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
open MeasureTheory Function Set StatMech Finset StatMech.Percolation


/--
[mem_withinConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma mem_withinConnEvent_eq
  {d : ℕ}
  {S : Set (Site d)}
  {o x : Site d}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ withinConnEvent d S o x ↔ ∃ (ho : o ∈ S) (hx : x ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨x, hx⟩ := by
-- proof
  apply StatMech.Percolation.mem_withinConnEvent

/--
[mem_edgesWithinFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma mem_edgesWithinFinset_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  e ∈ edgesWithinFinset S ↔ ∃ x ∈ S, ∃ y ∈ S, e = s(x, y) := by
-- proof
  apply StatMech.Percolation.mem_edgesWithinFinset

/--
[withinConn_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma withinConn_congr_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∀ e ∈ (edgesWithinFinset S : Set (Sym2 (Site d))), ω e = ω' e) :
-- imply
  ω ∈ withinConnEvent d (S : Set (Site d)) o x ↔ ω' ∈ withinConnEvent d (S : Set (Site d)) o x := by
-- proof
  apply StatMech.Percolation.withinConn_congr S o x h

/--
[withinConn_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma withinConn_dependsOn_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d} :
-- imply
  DependsOn ((withinConnEvent d (S : Set (Site d)) o x).indicator (fun _ => (1 : ℝ))) ((edgesWithinFinset S : Set (Sym2 (Site d)))) := by
-- proof
  apply StatMech.Percolation.withinConn_dependsOn S o x

/--
[withinConnEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma withinConnEvent_eq_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (h0 : origin d ∈ (S : Set (Site d)))
  (hx : x ∈ (S : Set (Site d))) :
-- imply
  withinConnEvent d (S : Set (Site d)) (origin d) x = {ω | ConnectedWithin d ω (S : Set (Site d)) ⟨origin d, h0⟩ ⟨x, hx⟩} := by
-- proof
  apply StatMech.Percolation.withinConnEvent_eq S x h0 hx

/--
[connWithinProb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma connWithinProb_eq_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : origin d ∈ (S : Set (Site d)))
  (hx : x ∈ (S : Set (Site d))) :
-- imply
  connWithinProb d p hp S x = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) x) := by
-- proof
  apply StatMech.Percolation.connWithinProb_eq p hp S x h0 hx

/--
[withinConn_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma withinConn_indep_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o x : Site d}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hdisj : Disjoint (edgesWithinFinset S) U)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) o x ∩ B) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) o x) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
-- proof
  apply StatMech.Percolation.withinConn_indep p hp S o x B U hdisj hB

/--
[boundaryEdges_fst_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma boundaryEdges_fst_mem_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (he : e ∈ boundaryEdges d S) :
-- imply
  e.1 ∈ S := by
-- proof
  apply StatMech.Percolation.boundaryEdges_fst_mem he

/--
[phi_reassembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma phi_reassembly_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : origin d ∈ S)
  (hdisj : Disjoint (edgesWithinFinset S) U)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (p : ℝ) * ∑ e ∈ boundaryEdges d S, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ B) = phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
-- proof
  apply StatMech.Percolation.phi_reassembly p hp S h0 B U hdisj hB

/--
[phi_surface_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferentialFull.lean)
-/
@[path]
private lemma phi_surface_summand_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : origin d ∈ S)
  (hp0 : 0 < (p : ℝ))
  (hp1 : (p : ℝ) < 1)
  (hdisj : Disjoint (edgesWithinFinset S) U)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (1 / (1 - (p : ℝ))) * ∑ e ∈ boundaryEdges d S, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ B) = (1 / ((p : ℝ) * (1 - (p : ℝ)))) * (phi d p hp S * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B) := by
-- proof
  apply StatMech.Percolation.phi_surface_summand p hp S h0 hp0 hp1 B U hdisj hB


-- created on 2026-10-23

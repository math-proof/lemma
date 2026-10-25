import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tex_threeDistinctInfinite_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_threeDistinctInfinite_of_threeMeetBox_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  tex_ThreeDistinctInfinite ω := by
-- proof
  apply StatMech.Percolation.tex_threeDistinctInfinite_of_threeMeetBox hω

/--
[tex_insertion_of_attachData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_insertion_of_attachData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃)
  (h : tex_AttachData ω x₁ x₂ x₃) :
-- imply
  tre_MergeFreeInsertion ω := by
-- proof
  apply StatMech.Percolation.tex_insertion_of_attachData ω x₁ x₂ x₃ hd h

/--
[tex_threeClustersReachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_threeClustersReachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃)
  (h : tex_AttachData ω x₁ x₂ x₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tex_threeClustersReachOrigin ω x₁ x₂ x₃ hd h

/--
[tex_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_mergeFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃)
  (h : tex_AttachData ω x₁ x₂ x₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), bka_MergeFree (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tex_mergeFree ω x₁ x₂ x₃ hd h

/--
[tex_boxMengerAttachment_of_boxAttachData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_boxMengerAttachment_of_boxAttachData_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tex_BoxAttachData d n) :
-- imply
  bmm_BoxMengerAttachment d n := by
-- proof
  apply StatMech.Percolation.tex_boxMengerAttachment_of_boxAttachData h

/--
[tex_threeClustersReachOrigin_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_threeClustersReachOrigin_of_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tex_BoxAttachData d n) :
-- imply
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tex_threeClustersReachOrigin_of_box h

/--
[tex_disjointRouting_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_disjointRouting_of_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : tex_BoxAttachData d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.tex_disjointRouting_of_box h

/--
[tex_attachData_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_attachData_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.tex_attachData_of_neighbour_witnesses ω x₁ x₂ x₃ hadj hri

/--
[tex_threeClustersReachOrigin_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_threeClustersReachOrigin_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd : cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧ cluster d ω x₂ ≠ cluster d ω x₃)
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.tex_threeClustersReachOrigin_of_neighbour_witnesses ω x₁ x₂ x₃ hd hadj hri

/--
[tex_boxAttachData_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence2.lean)
-/
@[path]
private lemma tex_boxAttachData_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.tex_boxAttachData_nonvacuous ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23

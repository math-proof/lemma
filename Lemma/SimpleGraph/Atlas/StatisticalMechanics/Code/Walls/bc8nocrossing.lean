import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc8nocrossing.Part2
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc8_clusters_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_clusters_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ¬ Connected d (removeSite 0 ω) x y) :
-- imply
  Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) := by
-- proof
  apply StatMech.Walls.bc8_clusters_disjoint h

/--
[bc8_connected_of_not_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_connected_of_not_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ¬ Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y)) :
-- imply
  Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc8_connected_of_not_disjoint h

/--
[bc8_cut_disjoint_iff_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_cut_disjoint_iff_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) ↔ ¬ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc8_cut_disjoint_iff_disconnected

/--
[bc8_cut_ne_iff_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_cut_ne_iff_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔ ¬ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc8_cut_ne_iff_disconnected

/--
[bc8_cut_ne_iff_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_cut_ne_iff_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔ Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) := by
-- proof
  apply StatMech.Walls.bc8_cut_ne_iff_disjoint

/--
[bc8_disjoint_of_cut_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_disjoint_of_cut_ne_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
-- imply
  Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) := by
-- proof
  apply StatMech.Walls.bc8_disjoint_of_cut_ne hne

/--
[bc8_cut_no_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_cut_no_crossing_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y) :
-- imply
  ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y → ¬ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc8_cut_no_crossing hne

/--
[bc8_cut_no_crossing_of_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_cut_no_crossing_of_disconnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ¬ Connected d (removeSite 0 ω) x y) :
-- imply
  ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y → ¬ IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc8_cut_no_crossing_of_disconnected h

/--
[bc8_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_noCrossing_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  bc8_NoCrossing ω x y := by
-- proof
  apply StatMech.Walls.bc8_noCrossing ω x y

/--
[bc8_threeArms_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_threeArms_pairwiseDisjoint_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite ∧ Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₂') ∧ Disjoint (cluster d (removeSite 0 ω) x₁') (cluster d (removeSite 0 ω) x₃') ∧ Disjoint (cluster d (removeSite 0 ω) x₂') (cluster d (removeSite 0 ω) x₃') ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₂' → ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₁' → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' → ¬ IsOpenEdge d (removeSite 0 ω) u v) ∧ (∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x₂' → ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) x₃' → ¬ IsOpenEdge d (removeSite 0 ω) u v) := by
-- proof
  apply StatMech.Walls.bc8_threeArms_pairwiseDisjoint n ω hω

/--
[bc8_threeArms_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean)
-/
@[path]
private lemma bc8_threeArms_noCrossing_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ x₁' x₂' x₃' : Site d, (cluster d (removeSite 0 ω) x₁').Infinite ∧ (cluster d (removeSite 0 ω) x₂').Infinite ∧ (cluster d (removeSite 0 ω) x₃').Infinite ∧ bc8_NoCrossing ω x₁' x₂' ∧ bc8_NoCrossing ω x₁' x₃' ∧ bc8_NoCrossing ω x₂' x₃' := by
-- proof
  apply StatMech.Walls.bc8_threeArms_noCrossing n ω hω


-- created on 2026-10-23

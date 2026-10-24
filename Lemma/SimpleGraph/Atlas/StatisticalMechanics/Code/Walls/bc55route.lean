import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc55route
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc55_hroute_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_hroute_of_routingCover_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc55_hroute_of_routingCover p hp1 hp0 hrt

/--
[bc55_hroute_of_boxMengerAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_hroute_of_boxMengerAttachment_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
-- imply
  ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc55_hroute_of_boxMengerAttachment p hp1 hp0 hattach

/--
[bc55_burton_keane_bernoulli_of_boxMenger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_burton_keane_bernoulli_of_boxMenger_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc55_burton_keane_bernoulli_of_boxMenger hd p hp1 hp0 hattach

/--
[bc55_burton_keane_bernoulli_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_burton_keane_bernoulli_of_routingCover_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc55_burton_keane_bernoulli_of_routingCover hd p hp1 hp0 hrt

/--
[bc55_boxMenger_forces_originNeighbour_in_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_boxMenger_forces_originNeighbour_in_cluster_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hattach : bmm_BoxMengerAttachment d n)
  (hω : ω ∈ threeMeetBox d n)
  (hb1 : x₁ ∈ box d n)
  (hb2 : x₂ ∈ box d n)
  (hb3 : x₃ ∈ box d n)
  (hi1 : (cluster d ω x₁).Infinite)
  (hi2 : (cluster d ω x₂).Infinite)
  (hi3 : (cluster d ω x₃).Infinite)
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
-- imply
  (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₁) ∧ (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₂) ∧ (∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x₃) := by
-- proof
  apply StatMech.Walls.bc55_boxMenger_forces_originNeighbour_in_cluster n hattach ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23

/--
[bc55_originNeighbour_avoiding_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_originNeighbour_avoiding_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hno : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ∉ cluster d ω x) :
-- imply
  ¬ ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x := by
-- proof
  apply StatMech.Walls.bc55_originNeighbour_avoiding_cluster ω x hno

/--
[bc55_naive_collapse_false_of_notNeighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_naive_collapse_false_of_notNeighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hxne : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ≠ x) :
-- imply
  ¬ ((hypercubicLattice d).Adj 0 x ∧ x ∈ cluster d ω x) := by
-- proof
  apply StatMech.Walls.bc55_naive_collapse_false_of_notNeighbour ω x hxne

/--
[bc55_boxMenger_zeroObstacle_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_boxMenger_zeroObstacle_witness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ∃ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))), ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (∀ e ∈ W, (0 : Site d) ∉ e) ∧ (a₁ ∈ cluster d ω x₁ ∧ a₂ ∈ cluster d ω x₂ ∧ a₃ ∈ cluster d ω x₃) ∧ ((∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁) ∧ (∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂) ∧ (∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)) ∧ (Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂ ∧ Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃) ∧ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) := by
-- proof
  apply StatMech.Walls.bc55_boxMenger_zeroObstacle_witness ω x₁ x₂ x₃ hadj hri

/--
[bc55_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc55route.lean)
-/
@[path]
private lemma bc55_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p) :
-- imply
  ((∀ n : ℕ, bmm_BoxMengerAttachment d n) → ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) ∧ ((∀ n : ℕ, bmm_BoxMengerAttachment d n) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0) := by
-- proof
  apply StatMech.Walls.bc55_status hd p hp1 hp0


-- created on 2026-10-23

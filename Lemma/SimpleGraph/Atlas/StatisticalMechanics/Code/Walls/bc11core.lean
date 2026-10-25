import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc11core.Part2
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths MeasureTheory StatMech StatMech.Walls


/--
[bc11_boxOriginReach_of_openReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_boxOriginReach_of_openReach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc11_BoxOriginOpenReach d n) :
-- imply
  bc9_BoxOriginReach d n := by
-- proof
  apply StatMech.Walls.bc11_boxOriginReach_of_openReach n h

/--
[bc11_originRewiring_of_openReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_originRewiring_of_openReach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc11_BoxOriginOpenReach d n) :
-- imply
  bc8_OriginRewiring d n := by
-- proof
  apply StatMech.Walls.bc11_originRewiring_of_openReach n h

/--
[bc11_canonicalTrif_of_openReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_canonicalTrif_of_openReach_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bc11_BoxOriginOpenReach d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
-- proof
  apply StatMech.Walls.bc11_canonicalTrif_of_openReach n h ω hω

/--
[bc11_burtonKeane_uniqueness_of_openReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_burtonKeane_uniqueness_of_openReach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hr : ∀ n : ℕ, bc11_BoxOriginOpenReach d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc11_burtonKeane_uniqueness_of_openReach μ herg hfe bdry hbound hvol hdens hr

/--
[bc11_boxOriginOpenReach_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_boxOriginOpenReach_of_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {y₁ y₂ y₃ : Site d}
  {R₁ R₂ R₃ : Set (Site d)}
-- given
  (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hy1 : y₁ ≠ 0)
  (hy2 : y₂ ≠ 0)
  (hy3 : y₃ ≠ 0)
  (hc1 : Connected d (forceOpenFinset W ω) 0 y₁)
  (hc2 : Connected d (forceOpenFinset W ω) 0 y₂)
  (hc3 : Connected d (forceOpenFinset W ω) 0 y₃)
  (hbi1 : (cluster d (removeSite 0 ω) y₁).Infinite)
  (hbi2 : (cluster d (removeSite 0 ω) y₂).Infinite)
  (hbi3 : (cluster d (removeSite 0 ω) y₃).Infinite)
  (hm1 : y₁ ∈ R₁)
  (hm2 : y₂ ∈ R₂)
  (hm3 : y₃ ∈ R₃)
  (ho1 : ∀ u v, u ∈ R₁ → IsOpenEdge d ω u v → v ∈ R₁)
  (ho2 : ∀ u v, u ∈ R₂ → IsOpenEdge d ω u v → v ∈ R₂)
  (ho3 : ∀ u v, u ∈ R₃ → IsOpenEdge d ω u v → v ∈ R₃)
  (hg1 : ∀ u v, u ∈ R₁ → s(u, v) ∈ W → v ∈ R₁)
  (hg2 : ∀ u v, u ∈ R₂ → s(u, v) ∈ W → v ∈ R₂)
  (hg3 : ∀ u v, u ∈ R₃ → s(u, v) ∈ W → v ∈ R₃)
  (hd12 : Disjoint R₁ R₂)
  (hd13 : Disjoint R₁ R₃)
  (hd23 : Disjoint R₂ R₃) :
-- imply
  ∃ W' : Finset (Sym2 (Site d)), (∀ e ∈ W', (0 : Site d) ∉ e) ∧ ∃ z₁ z₂ z₃ : Site d, ∃ S₁ S₂ S₃ : Set (Site d), z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ z₃ ≠ 0 ∧ Connected d (forceOpenFinset W' ω) 0 z₁ ∧ Connected d (forceOpenFinset W' ω) 0 z₂ ∧ Connected d (forceOpenFinset W' ω) 0 z₃ ∧ (cluster d (removeSite 0 ω) z₁).Infinite ∧ (cluster d (removeSite 0 ω) z₂).Infinite ∧ (cluster d (removeSite 0 ω) z₃).Infinite ∧ (z₁ ∈ S₁ ∧ z₂ ∈ S₂ ∧ z₃ ∈ S₃) ∧ ((∀ u v, u ∈ S₁ → IsOpenEdge d ω u v → v ∈ S₁) ∧ (∀ u v, u ∈ S₂ → IsOpenEdge d ω u v → v ∈ S₂) ∧ (∀ u v, u ∈ S₃ → IsOpenEdge d ω u v → v ∈ S₃)) ∧ ((∀ u v, u ∈ S₁ → s(u, v) ∈ W' → v ∈ S₁) ∧ (∀ u v, u ∈ S₂ → s(u, v) ∈ W' → v ∈ S₂) ∧ (∀ u v, u ∈ S₃ → s(u, v) ∈ W' → v ∈ S₃)) ∧ (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) := by
-- proof
  apply StatMech.Walls.bc11_boxOriginOpenReach_of_reach ω W hW0 hy1 hy2 hy3 hc1 hc2 hc3 hbi1 hbi2 hbi3 hm1 hm2 hm3 ho1 ho2 ho3 hg1 hg2 hg3 hd12 hd13 hd23

/--
[bc11_origin_openReach_needs_base_open_nbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_origin_openReach_needs_base_open_nbr_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {y : Site d}
-- given
  (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hy : y ≠ 0)
  (hconn : Connected d (forceOpenFinset W ω) 0 y) :
-- imply
  ∃ v : Site d, (hypercubicLattice d).Adj 0 v ∧ ω s((0 : Site d), v) = true := by
-- proof
  apply StatMech.Walls.bc11_origin_openReach_needs_base_open_nbr ω W hW0 hy hconn

/--
[bc11_isolated_origin_no_openReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_isolated_origin_no_openReach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {y : Site d}
-- given
  (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
  (hiso : ∀ v : Site d, ¬ (openSubgraph d ω).Adj 0 v)
  (hy : y ≠ 0)
  (hconn : Connected d (forceOpenFinset W ω) 0 y) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc11_isolated_origin_no_openReach ω W hW0 hiso hy hconn

/--
[bc11_boxReach_of_attachData_unpacked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_boxReach_of_attachData_unpacked_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {W : Finset (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj1 : (hypercubicLattice d).Adj 0 a₁)
  (hadj2 : (hypercubicLattice d).Adj 0 a₂)
  (hadj3 : (hypercubicLattice d).Adj 0 a₃)
  (hW0 : ∀ e ∈ W, (0 : Site d) ∉ e)
  (ha1 : a₁ ∈ cluster d ω x₁)
  (ha2 : a₂ ∈ cluster d ω x₂)
  (ha3 : a₃ ∈ cluster d ω x₃)
  (hg1 : ∀ u v, u ∈ cluster d ω x₁ → s(u, v) ∈ W → v ∈ cluster d ω x₁)
  (hg2 : ∀ u v, u ∈ cluster d ω x₂ → s(u, v) ∈ W → v ∈ cluster d ω x₂)
  (hg3 : ∀ u v, u ∈ cluster d ω x₃ → s(u, v) ∈ W → v ∈ cluster d ω x₃)
  (hcr1 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₁ x₁)
  (hcr2 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₂ x₂)
  (hcr3 : Connected d (removeSite 0 (forceOpenFinset W ω)) a₃ x₃)
  (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite)
  (hd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (ho1 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁)
  (ho2 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂)
  (ho3 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) :
-- imply
  ∃ W' : Finset (Sym2 (Site d)), (∀ e ∈ W', (0 : Site d) ∉ e) ∧ ∃ y₁ y₂ y₃ : Site d, y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧ Connected d (forceOpenFinset W' ω) 0 y₁ ∧ Connected d (forceOpenFinset W' ω) 0 y₂ ∧ Connected d (forceOpenFinset W' ω) 0 y₃ ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃).Infinite ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ := by
-- proof
  apply StatMech.Walls.bc11_boxReach_of_attachData_unpacked ω a₁ a₂ a₃ W x₁ x₂ x₃ hadj1 hadj2 hadj3 hW0 ha1 ha2 ha3 hg1 hg2 hg3 hcr1 hcr2 hcr3 hi1 hi2 hi3 hd12 hd13 hd23 ho1 ho2 ho3

/--
[bc11_boxReach_of_attachData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_boxReach_of_attachData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h : tex_AttachData ω x₁ x₂ x₃)
  (hopen : ∀ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))), (∀ e ∈ W, (0 : Site d) ∉ e) → (hypercubicLattice d).Adj 0 a₁ → (hypercubicLattice d).Adj 0 a₂ → (hypercubicLattice d).Adj 0 a₃ → a₁ ∈ cluster d ω x₁ → a₂ ∈ cluster d ω x₂ → a₃ ∈ cluster d ω x₃ → (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧ (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧ (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃) :
-- imply
  ∃ W' : Finset (Sym2 (Site d)), (∀ e ∈ W', (0 : Site d) ∉ e) ∧ ∃ y₁ y₂ y₃ : Site d, y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧ Connected d (forceOpenFinset W' ω) 0 y₁ ∧ Connected d (forceOpenFinset W' ω) 0 y₂ ∧ Connected d (forceOpenFinset W' ω) 0 y₃ ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃).Infinite ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₁ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ ∧ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₂ ≠ cluster d (removeSite 0 (forceOpenFinset W' ω)) y₃ := by
-- proof
  apply StatMech.Walls.bc11_boxReach_of_attachData ω x₁ x₂ x₃ hd12 hd13 hd23 h hopen

/--
[bc11_boxOriginReach_of_attachData_and_openIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_boxOriginReach_of_attachData_and_openIncidence_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hattach : tex_BoxAttachData d n)
  (hinc : bc11_BoxOriginOpenIncidence d n) :
-- imply
  bc9_BoxOriginReach d n := by
-- proof
  apply StatMech.Walls.bc11_boxOriginReach_of_attachData_and_openIncidence n hattach hinc

/--
[bc11_originRewiring_of_attachData_and_openIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean)
-/
@[path]
private lemma bc11_originRewiring_of_attachData_and_openIncidence_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hattach : tex_BoxAttachData d n)
  (hinc : bc11_BoxOriginOpenIncidence d n) :
-- imply
  bc8_OriginRewiring d n := by
-- proof
  apply StatMech.Walls.bc11_originRewiring_of_attachData_and_openIncidence n hattach hinc


-- created on 2026-10-23

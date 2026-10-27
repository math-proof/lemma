import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossingUncond.Part3
open Set MeasureTheory SimpleGraph StatMech StatMech.RSW StatMech.RSW.Uncond


/--
[mem_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma mem_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ y : Site 2} :
-- imply
  y ∈ leftReach ω x₀ ↔ Connected 2 ω x₀ y := by
-- proof
  apply StatMech.RSW.Uncond.mem_leftReach

/--
[self_mem_leftReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma self_mem_leftReach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2} :
-- imply
  x₀ ∈ leftReach ω x₀ := by
-- proof
  apply StatMech.RSW.Uncond.self_mem_leftReach ω x₀

/--
[noPrimalConn_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma noPrimalConn_separated_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {y₀ : Site 2}
-- given
  (hy₀ : ¬ Connected 2 ω x₀ y₀) :
-- imply
  ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ := by
-- proof
  apply StatMech.RSW.Uncond.noPrimalConn_separated ω x₀ hy₀

/--
[noPrimalConn_dualBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma noPrimalConn_dualBarrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
-- imply
  ω s(x, y) = false ∧ dualConfig ω (crossEdge s(x, y)) = true := by
-- proof
  apply StatMech.RSW.Uncond.noPrimalConn_dualBarrier ω x₀ hadj hmem

/--
[escape_crosses_dualBarrier_oddly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma escape_crosses_dualBarrier_oddly_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {y : Site 2}
  {w : (hypercubicLattice 2).Walk x₀ y}
-- given
  (hy : ¬ Connected 2 ω x₀ y) :
-- imply
  ¬ Even (crossCount (leftReach ω x₀) w) := by
-- proof
  apply StatMech.RSW.Uncond.escape_crosses_dualBarrier_oddly ω x₀ hy w

/--
[dualBarrierExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma dualBarrierExists_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {y₀ : Site 2}
  {w : (hypercubicLattice 2).Walk x₀ y₀}
-- given
  (hfin : (cluster 2 ω x₀).Finite)
  (hy₀ : ¬ Connected 2 ω x₀ y₀) :
-- imply
  (∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧ ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧ ∀ γ : (hypercubicLattice 2).Walk x₀ y₀, ¬ Even (crossCount (leftReach ω x₀) γ) := by
-- proof
  apply StatMech.RSW.Uncond.dualBarrierExists ω x₀ hfin w hy₀

/--
[primal_or_dualBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma primal_or_dualBarrier_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {y₀ : Site 2}
  {w : (hypercubicLattice 2).Walk x₀ y₀}
-- given
  (hfin : (cluster 2 ω x₀).Finite) :
-- imply
  Connected 2 ω x₀ y₀ ∨ ((∃ (u : Site 2) (c : (faceBoundaryGraph (leftReach ω x₀)).Walk u u), c.IsCycle) ∧ ¬ (latticeMinusBarrier (leftReach ω x₀)).Reachable x₀ y₀ ∧ (∀ γ : (hypercubicLattice 2).Walk x₀ y₀, ¬ Even (crossCount (leftReach ω x₀) γ))) := by
-- proof
  apply StatMech.RSW.Uncond.primal_or_dualBarrier ω x₀ hfin w

/--
[dualBarrier_isOpenDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma dualBarrier_isOpenDual_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {x₀ : Site 2}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hmem : s(x, y) ∈ bdEdgeSet2 (leftReach ω x₀)) :
-- imply
  dualConfig ω (crossEdge s(x, y)) = true := by
-- proof
  apply StatMech.RSW.Uncond.dualBarrier_isOpenDual ω x₀ hadj hmem

/--
[square_cross_ge_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma square_cross_ge_half_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
-- given
  (hsep : (squareCross n)ᶜ ⊆ squareDualCross n)
  (hselfDual : μ.real (squareDualCross n) = μ.real (squareCross n))
  (hmeas : MeasurableSet (squareCross n)) :
-- imply
  (1 : ℝ) / 2 ≤ μ.real (squareCross n) := by
-- proof
  apply StatMech.RSW.Uncond.square_cross_ge_half μ n hsep hselfDual hmeas

/--
[measureReal_boxCross_ge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma measureReal_boxCross_ge_halves_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsFiniteMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n) :
-- imply
  μ.real (boxLeftHalf n hn hz0 hzc hzd) * μ.real (boxRightHalf n hn hz0 hzc hzd) ≤ μ.real (boxCross n) := by
-- proof
  apply StatMech.RSW.Uncond.measureReal_boxCross_ge_halves μ hpa n hn hz0 hzc hzd

/--
[box_crossing_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma box_crossing_lower_bound_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n)
  (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
  (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
-- imply
  (1 : ℝ) / 4 ≤ μ.real (boxCross n) := by
-- proof
  apply StatMech.RSW.Uncond.box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hleft hright

/--
[box_crossing_lower_bound_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossingUncond.lean)
-/
@[path]
private lemma box_crossing_lower_bound_pos_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {n : ℤ}
  {z : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hn : 0 ≤ n)
  (hz0 : z 0 = n)
  (hzc : 0 ≤ z 1)
  (hzd : z 1 ≤ n)
  (hleft : (1 : ℝ) / 2 ≤ μ.real (boxLeftHalf n hn hz0 hzc hzd))
  (hright : (1 : ℝ) / 2 ≤ μ.real (boxRightHalf n hn hz0 hzc hzd)) :
-- imply
  ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (boxCross n) := by
-- proof
  apply StatMech.RSW.Uncond.box_crossing_lower_bound_pos μ hpa n hn hz0 hzc hzd hleft hright


-- created on 2026-10-23

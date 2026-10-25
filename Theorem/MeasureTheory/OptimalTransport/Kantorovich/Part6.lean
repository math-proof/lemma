/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/OptimalTransport/Kantorovich.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Order.Compact
import Def.MeasureTheory.OptimalTransport.Kantorovich.Part6


section

open MeasureTheory

open scoped BoundedContinuousFunction CompactlySupported ENNReal

namespace MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted

/--
Strong duality on nonempty compact metric Borel spaces: for continuous `c : X × Y → ℝ`, `inf_π ∫ c
dπ = sup_{φ,ψ} ∫ φ dμ + ∫ ψ dν` over couplings `π` and continuous potentials `φ, ψ` with `φ x + ψ y
≤ c (x,y)`.
Source: L. V. Kantorovich, On the Translocation of Masses (1942); English transl. J. Math. Sci. 133
(2006), 1381-1382, DOI 10.1007/S10958-006-0049-2; modern ref C. Villani, Topics in Optimal
Transportation (2003).

Proves `Wanted` entry `kantorovich_duality_compact`.
-/
theorem kantorovich_duality_compact
    {X Y : Type*}
    [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (c : X × Y → ℝ) (hc : Continuous c) :
    sInf (primalValues μ ν c) =
    sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} := by
  have hP : (primalValues μ ν c).Nonempty := primalValues_nonempty μ ν c
  have hD : {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}.Nonempty :=
    dualValues_nonempty μ ν c hc
  apply le_antisymm
  · have hε : ∀ ε : ℝ, 0 < ε → sInf (primalValues μ ν c) ≤ sSup {r : ℝ |
        ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
        DualFeasible c φ ψ ∧
        r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)} + ε := by
      intro ε hε
      obtain ⟨Pim, hpos, hPhi, hcost, hone⟩ := exists_posFunctional μ ν c hc ε hε
      obtain ⟨π, hcoup, hle⟩ :=
        coupling_of_posFunctional μ ν c hc _ ε Pim hpos hPhi hcost hone
      have hmem : (∫ p, c p ∂(π : Measure (X × Y))) ∈ primalValues μ ν c :=
        ⟨π, hcoup, rfl⟩
      have hbdd := primal_bddBelow μ ν c hc
      exact le_trans (csInf_le hbdd hmem) hle
    apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    have h := hε (b - sSup {r : ℝ | ∃ φ : X → ℝ, ∃ ψ : Y → ℝ,
      DualFeasible c φ ψ ∧
      r = (∫ x, φ x ∂(μ : Measure X)) + ∫ y, ψ y ∂(ν : Measure Y)}) (by linarith)
    linarith
  · apply csSup_le hD
    rintro r ⟨φ, ψ, hfeas, rfl⟩
    apply le_csInf hP
    rintro q ⟨π, hπ, rfl⟩
    obtain ⟨hφ, hψ, hle⟩ := hfeas
    exact dual_le_primal_of_isCoupling μ ν c hc φ ψ hφ hψ hle π hπ

end MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted
end

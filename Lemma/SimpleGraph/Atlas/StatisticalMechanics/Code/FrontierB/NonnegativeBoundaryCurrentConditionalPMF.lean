import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeBoundaryCurrentConditionalPMF
open MeasureTheory StatMech StatMech.FrontierB


/--
[boundaryNonnegativeParityPMF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeBoundaryCurrentConditionalPMF.lean)
-/
@[path]
private lemma boundaryNonnegativeParityPMF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {H : Finset (Sym2 V)}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior H = boundaryNonnegativeParityRawMass G beta J interior H * (ENNReal.ofReal (boundaryCurrentSum G beta J interior))⁻¹ := by
-- proof
  apply StatMech.FrontierB.boundaryNonnegativeParityPMF_apply G beta hbeta J hJ interior H

/--
[boundaryCurrentPMF_apply_eq_nonnegativeParity_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeBoundaryCurrentConditionalPMF.lean)
-/
@[path]
private lemma boundaryCurrentPMF_apply_eq_nonnegativeParity_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {m : EdgeCurrent G}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  boundaryCurrentPMF G beta J hbeta.le hJ interior m = boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior (currentParitySupport G m) * nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e) (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) (fun e : G.edgeFinset => e.1 ∈ currentParitySupport G m) m := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_apply_eq_nonnegativeParity_factor G beta hbeta J hJ interior m

/--
[boundaryCurrentPMF_eq_nonnegativeParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeBoundaryCurrentConditionalPMF.lean)
-/
@[path]
private lemma boundaryCurrentPMF_eq_nonnegativeParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  boundaryCurrentPMF G beta J hbeta.le hJ interior = (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior).bind (fun H => nonnegativeFiniteParityPMF G.edgeFinset (fun e => beta * J e) (fun e : G.edgeFinset => mul_nonneg hbeta.le (hJ e.1)) (fun e : G.edgeFinset => e.1 ∈ H)) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentPMF_eq_nonnegativeParity_bind G beta hbeta J hJ interior

/--
[boundaryCurrentFiniteMarginal_eq_nonnegativeParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeBoundaryCurrentConditionalPMF.lean)
-/
@[path]
private lemma boundaryCurrentFiniteMarginal_eq_nonnegativeParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {interior : Finset V}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  PMF.map (restrictCurrent S) (boundaryCurrentPMF G beta J hbeta.le hJ interior) = (PMF.map (restrictParity G S) (boundaryNonnegativeParityPMF G beta J hbeta.le hJ interior)).bind (nonnegativeFiniteParityPMF S (fun e : G.edgeFinset => beta * J e.1) (fun e : ↑S => mul_nonneg hbeta.le (hJ e.1.1))) := by
-- proof
  apply StatMech.FrontierB.boundaryCurrentFiniteMarginal_eq_nonnegativeParity_bind G beta hbeta J hJ interior S


-- created on 2026-10-23

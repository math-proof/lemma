import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentFiniteMarginal.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[nonnegativeParityPMF_map_restrictCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentFiniteMarginal.lean)
-/
@[path]
private lemma nonnegativeParityPMF_map_restrictCurrent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {lambda : Sym2 V → ℝ}
  {H : Finset (Sym2 V)}
  {S : Finset G.edgeFinset}
-- given
  (hlambda : ∀ e : G.edgeFinset, 0 ≤ lambda e.1) :
-- imply
  PMF.map (restrictCurrent S) (nonnegativeFiniteParityPMF G.edgeFinset lambda hlambda (fun e : G.edgeFinset => e.1 ∈ H)) = nonnegativeFiniteParityPMF S (fun e : G.edgeFinset => lambda e.1) (fun e : ↑S => hlambda e.1) (fun e : ↑S => e.1.1 ∈ H) := by
-- proof
  apply StatMech.FrontierB.nonnegativeParityPMF_map_restrictCurrent G lambda hlambda H S

/--
[sourcelessCurrentFiniteMarginal_eq_nonnegativeParity_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentFiniteMarginal.lean)
-/
@[path]
private lemma sourcelessCurrentFiniteMarginal_eq_nonnegativeParity_bind_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset G.edgeFinset}
-- given
  (hbeta : 0 < beta)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  PMF.map (restrictCurrent S) (sourcelessCurrentPMF G beta J hbeta.le hJ) = (PMF.map (restrictParity G S) (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ)).bind (nonnegativeFiniteParityPMF S (fun e : G.edgeFinset => beta * J e.1) (fun e : ↑S => mul_nonneg hbeta.le (hJ e.1.1))) := by
-- proof
  apply StatMech.FrontierB.sourcelessCurrentFiniteMarginal_eq_nonnegativeParity_bind G beta hbeta J hJ S


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.FKQ2SharpUncond
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptDisintegration


/--
[oqu_fk_q2_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKQ2SharpUncond.lean)
-/
@[path]
private lemma oqu_fk_q2_sharp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ}
  {n : ℕ}
  {σ : Fin n ≃ Sym2 V}
  {f : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hf : Monotone f)
  (hf0 : 0 ≤ f)
  (hf1 : ∀ ω, f ω ≤ 1) :
-- imply
  Lindeberg.var (fkMass G p 2) f ≤ ∑ e, AdaptMConditional.revealAdapt (fkMass G p 2) σ f e * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptDisintegration.oqu_fk_q2_sharp G hp hp1 σ hf hf0 hf1


-- created on 2026-10-23

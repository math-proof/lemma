import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.GlobalLSI
open Finset Real StatMech StatMech.Probability


/--
[gls_entCoord_eq_tpl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/GlobalLSI.lean)
-/
@[path]
private lemma gls_entCoord_eq_tpl_eq
  {n : ℕ}
  {p : ℝ}
  {g : ConfigSpace (Fin n) → ℝ}
  {e : Fin n}
  {ω : ConfigSpace (Fin n)} :
-- imply
  esd_entCoord p g e ω = tpl_ent (1 - p) (g (StatMech.setOpen e ω)) (g (StatMech.setClosed e ω)) := by
-- proof
  apply StatMech.Probability.gls_entCoord_eq_tpl p g e ω

/--
[gls_entCoord_le_deriv_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/GlobalLSI.lean)
-/
@[path]
private lemma gls_entCoord_le_deriv_sq_eq
  {n : ℕ}
  {p : ℝ}
  {f : ConfigSpace (Fin n) → ℝ}
  {e : Fin n}
  {ω : ConfigSpace (Fin n)}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_entCoord p (fun ω => (f ω) ^ 2) e ω ≤ (gls_deriv f e ω) ^ 2 := by
-- proof
  apply StatMech.Probability.gls_entCoord_le_deriv_sq hp0 hp1 f e ω

/--
[gls_globalLSI](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/GlobalLSI.lean)
-/
@[path]
private lemma gls_globalLSI_eq
  {n : ℕ}
  {p : ℝ}
  {f : ConfigSpace (Fin n) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) ≤ ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (gls_deriv f e ω) ^ 2) := by
-- proof
  apply StatMech.Probability.gls_globalLSI hp0 hp1 f

/--
[gls_globalLSI_weighted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/GlobalLSI.lean)
-/
@[path]
private lemma gls_globalLSI_weighted_eq
  {n : ℕ}
  {p : ℝ}
  {f : ConfigSpace (Fin n) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) (fun ω => (f ω) ^ 2) ≤ (1 / (p * (1 - p))) * ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (fun ω => p * (1 - p) * (gls_deriv f e ω) ^ 2) := by
-- proof
  apply StatMech.Probability.gls_globalLSI_weighted hp0 hp1 f


-- created on 2026-10-23

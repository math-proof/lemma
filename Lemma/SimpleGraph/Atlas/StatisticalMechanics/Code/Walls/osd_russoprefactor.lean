import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.osd_russoprefactor
open Real Finset StatMech StatMech.Walls


/--
[wall_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_prefactor_pos_eq
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β) :
-- imply
  0 < J / (Real.exp (β * J) - 1) := by
-- proof
  apply StatMech.Walls.wall_prefactor_pos hJ hβ

/--
[wall_prefactor_antitone_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_prefactor_antitone_beta_eq
  {J β β₀ : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β)
  (hββ : β ≤ β₀) :
-- imply
  J / (Real.exp (β₀ * J) - 1) ≤ J / (Real.exp (β * J) - 1) := by
-- proof
  apply StatMech.Walls.wall_prefactor_antitone_beta hJ hβ hββ

/--
[wall_minPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_minPrefactor_pos_eq
  [Fintype E]
  [Nonempty E]
  {g : E → ℝ}
-- given
  (hg : ∀ e, 0 < g e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ ∀ e, cR ≤ g e := by
-- proof
  apply StatMech.Walls.wall_minPrefactor_pos g hg

/--
[wall_oneSubExp_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_oneSubExp_pos_eq
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β) :
-- imply
  0 < 1 - Real.exp (-(β * J)) := by
-- proof
  apply StatMech.Walls.wall_oneSubExp_pos hJ hβ

/--
[wall_prefactor_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_prefactor_bridge_eq
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β) :
-- imply
  J / (Real.exp (β * J) - 1) = (J / (1 - Real.exp (-(β * J)))) * Real.exp (-(β * J)) := by
-- proof
  apply StatMech.Walls.wall_prefactor_bridge hJ hβ

/--
[wall_prefactor_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_prefactor_extraction_eq
  [Fintype E]
  {g Cov : E → ℝ}
  {cR : ℝ}
-- given
  (hg : ∀ e, cR ≤ g e)
  (hCov : ∀ e, 0 ≤ Cov e) :
-- imply
  cR * ∑ e, Cov e ≤ ∑ e, g e * Cov e := by
-- proof
  apply StatMech.Walls.wall_prefactor_extraction g Cov cR hg hCov

/--
[wall_russo_extraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_russo_extraction_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hCov : ∀ e, 0 ≤ Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ (∀ e, cR ≤ J e / (Real.exp (β * J e) - 1)) ∧ cR * ∑ e, Cov e ≤ ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e := by
-- proof
  apply StatMech.Walls.wall_russo_extraction J Cov β hJ hβ hCov

/--
[wall_russo_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_russo_prefactor_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β β₀ θ' : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hββ : β ≤ β₀)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ (∀ e, cR ≤ J e / (Real.exp (β₀ * J e) - 1)) ∧ cR * ∑ e, Cov e ≤ θ' := by
-- proof
  apply StatMech.Walls.wall_russo_prefactor J Cov β β₀ θ' hJ hβ hββ hCov hderiv

/--
[wall_russo_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/osd_russoprefactor.lean)
-/
@[path]
private lemma wall_russo_lower_bound_eq
  [Fintype E]
  [Nonempty E]
  {J Cov : E → ℝ}
  {β β₀ θ' : ℝ}
-- given
  (hJ : ∀ e, 0 < J e)
  (hβ : 0 < β)
  (hββ : β ≤ β₀)
  (hCov : ∀ e, 0 ≤ Cov e)
  (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
-- imply
  ∃ cR : ℝ, 0 < cR ∧ cR * (∑ e, Cov e) ≤ θ' := by
-- proof
  apply StatMech.Walls.wall_russo_lower_bound J Cov β β₀ θ' hJ hβ hββ hCov hderiv


-- created on 2026-10-23

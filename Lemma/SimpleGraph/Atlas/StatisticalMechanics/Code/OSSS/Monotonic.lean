import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
open Finset StatMech StatMech.OSSS StatMech.OSSS.Monotonic


/--
[agree_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma agree_self_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E}
  {η : ConfigSpace E} :
-- imply
  Agree F η η := by
-- proof
  apply StatMech.OSSS.Monotonic.agree_self F η

/--
[agree_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma agree_inf_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E}
  {ξ ζ a b : ConfigSpace E}
-- given
  (hle : ∀ f ∈ F, ξ f ≤ ζ f)
  (ha : Agree F ξ a)
  (hb : Agree F ζ b) :
-- imply
  Agree F ξ (a ⊓ b) := by
-- proof
  apply StatMech.OSSS.Monotonic.agree_inf F ξ ζ a b hle ha hb

/--
[agree_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma agree_sup_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E}
  {ξ ζ a b : ConfigSpace E}
-- given
  (hle : ∀ f ∈ F, ξ f ≤ ζ f)
  (ha : Agree F ξ a)
  (hb : Agree F ζ b) :
-- imply
  Agree F ζ (a ⊔ b) := by
-- proof
  apply StatMech.OSSS.Monotonic.agree_sup F ξ ζ a b hle ha hb

/--
[condNorm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma condNorm_pos_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 < condNorm μ F η := by
-- proof
  apply StatMech.OSSS.Monotonic.condNorm_pos hpos F η

/--
[condMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma condMass_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
-- given
  (hμ : 0 ≤ μ)
  (hZ : 0 < condNorm μ F η) :
-- imply
  0 ≤ condMass μ F η := by
-- proof
  apply StatMech.OSSS.Monotonic.condMass_nonneg hμ F η hZ

/--
[condMass_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma condMass_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {η : ConfigSpace E}
-- given
  (hZ : condNorm μ F η ≠ 0) :
-- imply
  ∑ ω, condMass μ F η ω = 1 := by
-- proof
  apply StatMech.OSSS.Monotonic.condMass_sum F η hZ

/--
[cross_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma cross_restricted_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {ξ ζ : ConfigSpace E}
  {a b : ConfigSpace E}
-- given
  (hμ : 0 ≤ μ)
  (hFKG : FKGLatticeCondition μ)
  (hle : ∀ f ∈ F, ξ f ≤ ζ f) :
-- imply
  (if Agree F ξ a then μ a else 0) * (if Agree F ζ b then μ b else 0) ≤ (if Agree F ξ (a ⊓ b) then μ (a ⊓ b) else 0) * (if Agree F ζ (a ⊔ b) then μ (a ⊔ b) else 0) := by
-- proof
  apply StatMech.OSSS.Monotonic.cross_restricted hμ hFKG F ξ ζ hle a b

/--
[cross_condMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma cross_condMass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {ξ ζ : ConfigSpace E}
  {a b : ConfigSpace E}
-- given
  (hμ : 0 ≤ μ)
  (hFKG : FKGLatticeCondition μ)
  (hle : ∀ f ∈ F, ξ f ≤ ζ f)
  (hZξ : 0 < condNorm μ F ξ)
  (hZζ : 0 < condNorm μ F ζ) :
-- imply
  condMass μ F ξ a * condMass μ F ζ b ≤ condMass μ F ξ (a ⊓ b) * condMass μ F ζ (a ⊔ b) := by
-- proof
  apply StatMech.OSSS.Monotonic.cross_condMass hμ hFKG F ξ ζ hle hZξ hZζ a b

/--
[isIncreasing_openAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma isIncreasing_openAt_eq
  [Fintype E]
  [DecidableEq E]
  {e : E} :
-- imply
  IsIncreasing (OpenAt (E := E) e) := by
-- proof
  apply StatMech.OSSS.Monotonic.isIncreasing_openAt e

/--
[fkg_implies_monotonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean)
-/
@[path]
private lemma fkg_implies_monotonic_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hFKG : FKGLatticeCondition μ) :
-- imply
  IsMonotonicMeasure μ := by
-- proof
  apply StatMech.OSSS.Monotonic.fkg_implies_monotonic hpos hFKG


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
open Set StatMech StatMech.Sharpness


/--
[tildeBetaCIsing_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma tildeBetaCIsing_nonneg_eq
  {d : ℕ} :
-- imply
  0 ≤ tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.tildeBetaCIsing_nonneg

/--
[bc_le_tildeBc_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma bc_le_tildeBc_ising_eq
  {d : ℕ}
-- given
  (hbdd : BddBelow (positiveMagnetizationSet d))
  (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β) :
-- imply
  betaC d ≤ tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.bc_le_tildeBc_ising hbdd hpos

/--
[tildeBc_le_bc_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma tildeBc_le_bc_ising_eq
  {d : ℕ}
-- given
  (hne : (positiveMagnetizationSet d).Nonempty)
  (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
-- imply
  tildeBetaCIsing d ≤ betaC d := by
-- proof
  apply StatMech.Sharpness.tildeBc_le_bc_ising hne hzero

/--
[bc_eq_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma bc_eq_ising_eq
  {d : ℕ}
-- given
  (hbdd : BddBelow (positiveMagnetizationSet d))
  (hne : (positiveMagnetizationSet d).Nonempty)
  (hpos : ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β)
  (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
-- imply
  betaC d = tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.bc_eq_ising hbdd hne hpos hzero

/--
[posMag_of_meanfield_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma posMag_of_meanfield_sqrt_eq
  {d : ℕ}
-- given
  (htc_pos : 0 < tildeBetaCIsing d)
  (hsqrt : ∀ β, tildeBetaCIsing d ≤ β → Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
-- imply
  ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
-- proof
  apply StatMech.Sharpness.posMag_of_meanfield_sqrt htc_pos hsqrt

/--
[posMag_of_meanfield_sqrt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma posMag_of_meanfield_sqrt_nonneg_eq
  {d : ℕ}
-- given
  (hsqrt : ∀ β, tildeBetaCIsing d ≤ β → Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β) :
-- imply
  ∀ β, tildeBetaCIsing d < β → 0 < magnetization d β := by
-- proof
  apply StatMech.Sharpness.posMag_of_meanfield_sqrt_nonneg hsqrt

/--
[positiveMagnetizationSet_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma positiveMagnetizationSet_bddBelow_eq
  {d : ℕ} :
-- imply
  BddBelow (positiveMagnetizationSet d) := by
-- proof
  apply StatMech.Sharpness.positiveMagnetizationSet_bddBelow

/--
[bc_eq_ising_of_items](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma bc_eq_ising_of_items_eq
  {d : ℕ}
-- given
  (hsqrt : ∀ β, tildeBetaCIsing d ≤ β → Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
  (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
-- imply
  betaC d = tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.bc_eq_ising_of_items hsqrt hzero

/--
[bc_eq_ising_of_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BcEqIsing.lean)
-/
@[path]
private lemma bc_eq_ising_of_meanfield_eq
  {d : ℕ}
-- given
  (htc_pos : 0 < tildeBetaCIsing d)
  (hbdd : BddBelow (positiveMagnetizationSet d))
  (hne : (positiveMagnetizationSet d).Nonempty)
  (hsqrt : ∀ β, tildeBetaCIsing d ≤ β → Real.sqrt (1 - (tildeBetaCIsing d / β) ^ 2) ≤ magnetization d β)
  (hzero : ∀ β, 0 ≤ β → β < tildeBetaCIsing d → magnetization d β = 0) :
-- imply
  betaC d = tildeBetaCIsing d := by
-- proof
  apply StatMech.Sharpness.bc_eq_ising_of_meanfield htc_pos hbdd hne hsqrt hzero


-- created on 2026-10-23

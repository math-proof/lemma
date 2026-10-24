import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicBallot
open StatMech StatMech.Universality


/--
[natCard_horizontalNoHit_le_endpointFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma natCard_horizontalNoHit_le_endpointFibers_eq
  {t : Nat}
  {level : Int} :
-- imply
  Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) ≤ Nat.card (VerticalChoicePathFamily t (level - 1) (level - 2)) + Nat.card (VerticalChoicePathFamily t (level - 1) (level - 1)) := by
-- proof
  apply StatMech.Universality.natCard_horizontalNoHit_le_endpointFibers t level

/--
[horizontalNoHit_weight_le_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma horizontalNoHit_weight_le_sqrt_eq
  {t : Nat}
  {level : Int} :
-- imply
  Nat.card (IsingHorizontalNoHitFamily t (level - 1) level) / (2 : Real) ^ t ≤ 2 * Real.sqrt (2 / (t + 1 : Real)) := by
-- proof
  apply StatMech.Universality.horizontalNoHit_weight_le_sqrt t level

/--
[horizontalNoHit_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma horizontalNoHit_diffusive_weight_le_eq
  {ρ : Nat}
  {level : Int}
-- given
  (hρ : 0 < ρ) :
-- imply
  Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level - 1) level) / (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
-- proof
  apply StatMech.Universality.horizontalNoHit_diffusive_weight_le ρ level hρ

/--
[horizontalNoHit_diffusive_weight_le_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma horizontalNoHit_diffusive_weight_le_upper_eq
  {ρ : Nat}
  {level : Int}
-- given
  (hρ : 0 < ρ) :
-- imply
  Nat.card (IsingHorizontalNoHitFamily (ρ * ρ) (level + 1) level) / (2 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
-- proof
  apply StatMech.Universality.horizontalNoHit_diffusive_weight_le_upper ρ level hρ

/--
[killedChoiceNoHitAll_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma killedChoiceNoHitAll_diffusive_weight_le_eq
  {R ρ : Nat}
  {p : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < ρ) :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) / (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
-- proof
  apply StatMech.Universality.killedChoiceNoHitAll_diffusive_weight_le R ρ p level hstart hρ

/--
[killedChoiceNoHitAll_diffusive_weight_le_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma killedChoiceNoHitAll_diffusive_weight_le_upper_eq
  {R ρ : Nat}
  {p : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 = level + 1)
  (hρ : 0 < ρ) :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceNoHitAll R (ρ * ρ) p level) / (4 : Real) ^ (ρ * ρ) ≤ 4 / (ρ : Real) := by
-- proof
  apply StatMech.Universality.killedChoiceNoHitAll_diffusive_weight_le_upper R ρ p level hstart hρ

/--
[isingLeapfrogKilledKernel_reflectedStart_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_reflectedStart_l1_le_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  (∑ q, |isingLeapfrogKilledKernel R t p q - isingLeapfrogKilledKernel R t p' q|) ≤ Nat.card (SurvivalExceptionalFirstHitFamilyAll R (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t + Nat.card (SurvivalExceptionalMirrorFamilyAll R (isingLeapfrogBoxInt p) level t) / (4 : Real) ^ t + Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) / (4 : Real) ^ t + Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p' level) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_reflectedStart_l1_le R t p p' level hmirror

/--
[isingLeapfrogKilledKernel_reflectedStart_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_reflectedStart_diffusive_l1_le_eq
  {R level ρ : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < ρ)
  (hleft : ρ + 1 ≤ level)
  (hright : level + 1 + ρ ≤ R) :
-- imply
  (∑ q, |isingLeapfrogKilledKernel R (ρ * ρ) p q - isingLeapfrogKilledKernel R (ρ * ρ) p' q|) ≤ 10 / (ρ : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_reflectedStart_diffusive_l1_le R level ρ p p' hstart hmirror hρ hleft hright


-- created on 2026-10-23

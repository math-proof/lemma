import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
open StatMech StatMech.Universality


/--
[isingLeapfrogStoppedKernel_eq_natCard_choicePath_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_eq_natCard_choicePath_div_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogStoppedKernel R t p q = Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_eq_natCard_choicePath_div R t p q

/--
[IsingLeapfrogKilledChoiceValid.start_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma start_not_boundary_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
-- given
  (h : IsingLeapfrogKilledChoiceValid R p bs) :
-- imply
  ¬ isingLeapfrogBoxBoundary R p := by
-- proof
  apply StatMech.Universality.IsingLeapfrogKilledChoiceValid.start_not_boundary R p bs h

/--
[IsingLeapfrogKilledChoiceValid.endpoint_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma endpoint_not_boundary_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
-- given
  (h : IsingLeapfrogKilledChoiceValid R p bs) :
-- imply
  ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p bs) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogKilledChoiceValid.endpoint_not_boundary R p bs h

/--
[isingLeapfrogKilledKernel_eq_natCard_choicePath_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_eq_natCard_choicePath_div_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogKilledKernel R t p q = Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_eq_natCard_choicePath_div R t p q

/--
[isingLeapfrogChoiceSteps_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogChoiceSteps_valid_eq
  {bs : List (Bool × Bool)} :
-- imply
  IsingDiagonalWalkStepsValid (isingLeapfrogChoiceSteps bs) := by
-- proof
  apply StatMech.Universality.isingLeapfrogChoiceSteps_valid bs

/--
[IsingLeapfrogKilledChoiceValid.run_boxInt_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma run_boxInt_eq_endpoint_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
-- given
  (h : IsingLeapfrogKilledChoiceValid R p bs) :
-- imply
  isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) = isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p) (isingLeapfrogChoiceSteps bs) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogKilledChoiceValid.run_boxInt_eq_endpoint R p bs h

/--
[IsingLeapfrogKilledChoiceValid.take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma take_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
  {k : Nat}
-- given
  (h : IsingLeapfrogKilledChoiceValid R p bs) :
-- imply
  IsingLeapfrogKilledChoiceValid R p (bs.take k) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogKilledChoiceValid.take R p bs h k

/--
[IsingLeapfrogKilledChoiceValid.staysInOpenBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma staysInOpenBox_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
-- given
  (h : IsingLeapfrogKilledChoiceValid R p bs) :
-- imply
  StaysInOpenBox R (isingLeapfrogBoxInt p) (isingLeapfrogChoiceSteps bs) := by
-- proof
  apply StatMech.Universality.IsingLeapfrogKilledChoiceValid.staysInOpenBox R p bs h

/--
[choiceSteps_encodeSteps_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma choiceSteps_encodeSteps_of_valid_eq
  {path : List (Int × Int)}
-- given
  (hvalid : IsingDiagonalWalkStepsValid path) :
-- imply
  isingLeapfrogChoiceSteps (isingLeapfrogEncodeSteps path) = path := by
-- proof
  apply StatMech.Universality.choiceSteps_encodeSteps_of_valid path hvalid

/--
[killedChoiceValid_encodeSteps_of_stays](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma killedChoiceValid_encodeSteps_of_stays_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {path : List (Int × Int)}
-- given
  (hvalid : IsingDiagonalWalkStepsValid path)
  (hstays : StaysInOpenBox R (isingLeapfrogBoxInt p) path) :
-- imply
  IsingLeapfrogKilledChoiceValid R p (isingLeapfrogEncodeSteps path) := by
-- proof
  apply StatMech.Universality.killedChoiceValid_encodeSteps_of_stays R p path hvalid hstays

/--
[isingLeapfrogBoxInt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogBoxInt_injective_eq
  {R : Nat} :
-- imply
  Function.Injective (@isingLeapfrogBoxInt R) := by
-- proof
  apply StatMech.Universality.isingLeapfrogBoxInt_injective

/--
[encodeSteps_choiceSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma encodeSteps_choiceSteps_eq
  {bs : List (Bool × Bool)} :
-- imply
  isingLeapfrogEncodeSteps (isingLeapfrogChoiceSteps bs) = bs := by
-- proof
  apply StatMech.Universality.encodeSteps_choiceSteps bs

/--
[natCard_killedChoiceFirstHitFamily_eq_surviving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma natCard_killedChoiceFirstHitFamily_eq_surviving_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) = Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) := by
-- proof
  apply StatMech.Universality.natCard_killedChoiceFirstHitFamily_eq_surviving R t p q level

/--
[natCard_killedChoicePathFamily_eq_hit_add_noHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma natCard_killedChoicePathFamily_eq_hit_add_noHit_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) = Nat.card (IsingLeapfrogKilledChoiceFirstHitFamily R t p q level) + Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
-- proof
  apply StatMech.Universality.natCard_killedChoicePathFamily_eq_hit_add_noHit R t p q level

/--
[isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  isingLeapfrogKilledKernel R t p q = Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q)) / (4 : Real) ^ t + Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_eq_survivingFirstHit_add_noHit R t p q level

/--
[isingLeapfrogKilledKernel_reflectedStart_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_reflectedStart_abs_le_eq
  {R t : Nat}
  {p p' q : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  |isingLeapfrogKilledKernel R t p q - isingLeapfrogKilledKernel R t p' q| ≤ (Nat.dist (Nat.card (SurvivingFirstHitFamily R (isingLeapfrogBoxInt p) level t (isingLeapfrogBoxInt q))) (Nat.card (SurvivingFirstHitFamily R (reflectedEndpoint level (isingLeapfrogBoxInt p)) level t (isingLeapfrogBoxInt q))) : Real) / (4 : Real) ^ t + Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / (4 : Real) ^ t + Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p' q level) / (4 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_reflectedStart_abs_le R t p p' q level hmirror

/--
[killedChoiceNoHitFamily_weight_le_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma killedChoiceNoHitFamily_weight_le_free_eq
  {R t : Nat}
  {p q : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) / (4 : Real) ^ t ≤ 2 / (t + 1 : Real) := by
-- proof
  apply StatMech.Universality.killedChoiceNoHitFamily_weight_le_free R t p q level

/--
[isingLeapfrogKilledKernel_reflectedStart_diffusive_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma isingLeapfrogKilledKernel_reflectedStart_diffusive_abs_le_eq
  {R level ρ : Nat}
  {p p' q : IsingLeapfrogBox R}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < ρ)
  (hleft : ρ + 1 ≤ level)
  (hright : level + 1 + ρ ≤ R) :
-- imply
  |isingLeapfrogKilledKernel R (ρ * ρ) p q - isingLeapfrogKilledKernel R (ρ * ρ) p' q| ≤ 8 / (ρ : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLeapfrogKilledKernel_reflectedStart_diffusive_abs_le R level ρ p p' q hmirror hstart hρ hleft hright

/--
[firstHitSplit_none_endpoint_fst_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma firstHitSplit_none_endpoint_fst_ne_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
-- given
  (hnone : isingDiagonalWalkFirstHitSplit? start level path = none) :
-- imply
  ∀ k, k ≤ path.length → (isingDiagonalWalkEndpoint start (path.take k)).1 ≠ level := by
-- proof
  apply StatMech.Universality.firstHitSplit_none_endpoint_fst_ne hnone

/--
[natCard_killedChoiceNoHitAll_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma natCard_killedChoiceNoHitAll_eq_sum_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) = ∑ q, Nat.card (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) := by
-- proof
  apply StatMech.Universality.natCard_killedChoiceNoHitAll_eq_sum R t p level

/--
[natCard_killedChoiceNoHitAll_le_horizontal_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean)
-/
@[path]
private lemma natCard_killedChoiceNoHitAll_le_horizontal_mul_pow_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  Nat.card (IsingLeapfrogKilledChoiceNoHitAll R t p level) ≤ Nat.card (IsingHorizontalNoHitFamily t (isingLeapfrogBoxInt p).1 level) * 2 ^ t := by
-- proof
  apply StatMech.Universality.natCard_killedChoiceNoHitAll_le_horizontal_mul_pow R t p level


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
open StatMech StatMech.Universality


/--
[finiteUniformCoupling_fiber_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma finiteUniformCoupling_fiber_l1_le_eq
  {Omega A : Type}
  [Fintype Omega]
  [Fintype A]
  [DecidableEq A]
  {e : Omega ≃ Omega}
  {f g : Omega → A} :
-- imply
  ∑ a : A, := by
-- proof
  apply StatMech.Universality.finiteUniformCoupling_fiber_l1_le e f g

/--
[couplingReflectSteps_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma couplingReflectSteps_length_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)} :
-- imply
  (isingDiagonalWalkCouplingReflectSteps start level path).length = path.length := by
-- proof
  apply StatMech.Universality.couplingReflectSteps_length start level path

/--
[couplingReflectSteps_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma couplingReflectSteps_valid_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)}
-- given
  (hvalid : IsingDiagonalWalkStepsValid path) :
-- imply
  IsingDiagonalWalkStepsValid (isingDiagonalWalkCouplingReflectSteps start level path) := by
-- proof
  apply StatMech.Universality.couplingReflectSteps_valid start level path hvalid

/--
[couplingReflectSteps_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma couplingReflectSteps_involutive_eq
  {start : Int × Int}
  {level : Int}
  {path : List (Int × Int)} :
-- imply
  isingDiagonalWalkCouplingReflectSteps (reflectedEndpoint level start) level (isingDiagonalWalkCouplingReflectSteps start level path) = path := by
-- proof
  apply StatMech.Universality.couplingReflectSteps_involutive start level path

/--
[couplingChoiceTransform_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma couplingChoiceTransform_involutive_eq
  {t : Nat}
  {start : Int × Int}
  {level : Int} :
-- imply
  Function.LeftInverse (isingLeapfrogCouplingChoiceTransform t (reflectedEndpoint level start) level) (isingLeapfrogCouplingChoiceTransform t start level) := by
-- proof
  apply StatMech.Universality.couplingChoiceTransform_involutive t start level

/--
[lineFreeEndpoint_choiceHorizontal_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma lineFreeEndpoint_choiceHorizontal_full_eq
  {bs : List (Bool × Bool)}
  {start : Int × Int} :
-- imply
  lineFreeEndpoint start.1 (bs.map Prod.fst) = (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).1 := by
-- proof
  apply StatMech.Universality.lineFreeEndpoint_choiceHorizontal_full bs start

/--
[natCard_choiceNoHitAll_le_horizontal_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma natCard_choiceNoHitAll_le_horizontal_mul_pow_eq
  {t : Nat}
  {start level : Int} :
-- imply
  Nat.card (IsingLeapfrogChoiceNoHitAll t start level) ≤ Nat.card (IsingHorizontalNoHitFamily t start level) * 2 ^ t := by
-- proof
  apply StatMech.Universality.natCard_choiceNoHitAll_le_horizontal_mul_pow t start level

/--
[antitoneWeight_sum_le_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma antitoneWeight_sum_le_uniform_eq
  {a b : Nat → Real}
  {N : Nat}
  {c : Real}
-- given
  (ha0 : ∀ k, k ≤ N → 0 ≤ a k)
  (hadec : ∀ k, k < N → a (k + 1) ≤ a k)
  (hb : ∀ k, k ≤ N → ∑ j ∈ Finset.range (k + 1), b j ≤ c * (k + 1 : Nat)) :
-- imply
  (∑ k ∈ Finset.range (N + 1), a k * b k) ≤ c * ∑ k ∈ Finset.range (N + 1), a k := by
-- proof
  apply StatMech.Universality.antitoneWeight_sum_le_uniform a b N c ha0 hadec hb

/--
[sum_one_div_sqrt_succ_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma sum_one_div_sqrt_succ_le_eq
  {N : Nat} :
-- imply
  (∑ k ∈ Finset.range (N + 1), 1 / Real.sqrt (k + 1 : Real)) ≤ 2 * Real.sqrt (N + 1 : Real) := by
-- proof
  apply StatMech.Universality.sum_one_div_sqrt_succ_le N

/--
[ballotWeight_firstHit_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma ballotWeight_firstHit_sum_le_eq
  {rho N : Nat}
  {b : Nat → Real}
-- given
  (hρ : 0 < rho)
  (hN : N ≤ rho * rho)
  (hb : ∀ k, k ≤ N → ∑ j ∈ Finset.range (k + 1), b j ≤ (k + 1 : Real) / (rho : Real) ^ 2) :
-- imply
  (∑ k ∈ Finset.range (N + 1), (4 / Real.sqrt (k + 1 : Real)) * b k) ≤ 16 / (rho : Real) := by
-- proof
  apply StatMech.Universality.ballotWeight_firstHit_sum_le rho N b hρ hN hb

/--
[isingLineStoppedMean_centeredSq_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma isingLineStoppedMean_centeredSq_le_eq
  {m t : Nat}
  {p : IsingLineBox (2 * m)} :
-- imply
  isingLineStoppedMean (2 * m) t (isingLineCenteredSq m) p ≤ isingLineCenteredSq m p + (t : Real) := by
-- proof
  apply StatMech.Universality.isingLineStoppedMean_centeredSq_le m t p

/--
[isingLineStoppedKernel_center_boundary_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma isingLineStoppedKernel_center_boundary_le_eq
  {m t : Nat}
-- given
  (hm : 0 < m) :
-- imply
  isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨0, by omega⟩ + isingLineStoppedKernel (2 * m) t ⟨m, by omega⟩ ⟨2 * m, by omega⟩ ≤ (t : Real) / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_center_boundary_le m t hm

/--
[lineFirstBoundary_partial_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma lineFirstBoundary_partial_weight_le_eq
  {m K : Nat}
-- given
  (hm : 0 < m) :
-- imply
  (∑ j ∈ Finset.range (K + 1), (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) / (2 : Real) ^ j) ≤ (K : Real) / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.lineFirstBoundary_partial_weight_le m K hm

/--
[transverseRaceWitness_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma transverseRaceWitness_diffusive_weight_le_eq
  {rho m : Nat}
  {level : Int}
-- given
  (hρ : 0 < rho)
  (hm : rho ≤ m) :
-- imply
  Nat.card (IsingTransverseRaceWitnessFamily m (rho * rho) level) / (4 : Real) ^ (rho * rho) ≤ 16 / (rho : Real) := by
-- proof
  apply StatMech.Universality.transverseRaceWitness_diffusive_weight_le rho m level hρ hm

/--
[horizontalEscape_weight_le_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma horizontalEscape_weight_le_inv_eq
  {n t : Nat}
-- given
  (hn : 0 < n) :
-- imply
  Nat.card (IsingLeapfrogHorizontalEscapeFamily n t) / (4 : Real) ^ t ≤ 1 / (n : Real) := by
-- proof
  apply StatMech.Universality.horizontalEscape_weight_le_inv n t hn

/--
[choiceNoHitAll_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma choiceNoHitAll_diffusive_weight_le_eq
  {rho : Nat}
  {level : Int}
-- given
  (hρ : 0 < rho) :
-- imply
  Nat.card (IsingLeapfrogChoiceNoHitAll (rho * rho) (level - 1) level) / (4 : Real) ^ (rho * rho) ≤ 4 / (rho : Real) := by
-- proof
  apply StatMech.Universality.choiceNoHitAll_diffusive_weight_le rho level hρ

/--
[isingLeapfrogChoiceRun_append_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma isingLeapfrogChoiceRun_append_full_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {a b : List (Bool × Bool)} :
-- imply
  isingLeapfrogChoiceRun R p (a ++ b) = isingLeapfrogChoiceRun R (isingLeapfrogChoiceRun R p a) b := by
-- proof
  apply StatMech.Universality.isingLeapfrogChoiceRun_append_full R p a b

/--
[choiceExecValid_run_boxInt_eq_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma choiceExecValid_run_boxInt_eq_endpoint_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)}
-- given
  (h : IsingLeapfrogChoiceExecValid R p bs) :
-- imply
  isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p bs) = isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p) (isingLeapfrogChoiceSteps bs) := by
-- proof
  apply StatMech.Universality.choiceExecValid_run_boxInt_eq_endpoint R p bs h

/--
[couplingChoiceTransform_take_steps_of_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma couplingChoiceTransform_take_steps_of_some_eq
  {t : Nat}
  {start : Int × Int}
  {level : Int}
  {w : IsingLeapfrogChoiceStringFamily t}
  {split : IsingDiagonalWalkHitSplit start level}
-- given
  (hsplit : isingDiagonalWalkFirstHitSplit? start level (isingLeapfrogChoiceSteps w.1) = some split) :
-- imply
  isingLeapfrogChoiceSteps ((isingLeapfrogCouplingChoiceTransform t start level w).1.take split.before.length) = split.before.map reflectIncrement := by
-- proof
  apply StatMech.Universality.couplingChoiceTransform_take_steps_of_some t start level w split hsplit

/--
[stoppedCoupling_endpoints_eq_of_execValid_to_hit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma stoppedCoupling_endpoints_eq_of_execValid_to_hit_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int}
  {w : IsingLeapfrogChoiceStringFamily t}
  {split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p))
  (hsplit : isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level (isingLeapfrogChoiceSteps w.1) = some split)
  (hsource : IsingLeapfrogChoiceExecValid R p (w.1.take split.before.length))
  (hmirrorValid : IsingLeapfrogChoiceExecValid R p' ((isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) level w).1.take split.before.length)) :
-- imply
  isingLeapfrogChoiceRun R p w.1 = isingLeapfrogChoiceRun R p' (isingLeapfrogCouplingChoiceTransform t (isingLeapfrogBoxInt p) level w).1 := by
-- proof
  apply StatMech.Universality.stoppedCoupling_endpoints_eq_of_execValid_to_hit R t p p' level hmirror w split hsplit hsource hmirrorValid

/--
[stoppedCouplingBad_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma stoppedCouplingBad_cases_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int}
  {w : IsingLeapfrogStoppedCouplingBadFamily R t p p' level}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  (∀ k, k ≤ t → lineFreeEndpoint (isingLeapfrogBoxInt p).1 ((w.1.1.map Prod.fst).take k) ≠ level) ∨ IsingStoppedCouplingSourceFailure R p level w.1 ∨ IsingStoppedCouplingMirrorFailure R p p' level w.1 := by
-- proof
  apply StatMech.Universality.stoppedCouplingBad_cases R t p p' level hmirror w

/--
[natCard_stoppedCouplingBad_le_noHit_add_failures](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma natCard_stoppedCouplingBad_le_noHit_add_failures_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  Nat.card (IsingLeapfrogStoppedCouplingBadFamily R t p p' level) ≤ Nat.card (IsingLeapfrogChoiceNoHitAll t (isingLeapfrogBoxInt p).1 level) + Nat.card (IsingStoppedCouplingSourceFailureFamily R t p level) + Nat.card (IsingStoppedCouplingMirrorFailureFamily R t p p' level) := by
-- proof
  apply StatMech.Universality.natCard_stoppedCouplingBad_le_noHit_add_failures R t p p' level hmirror

/--
[lineChoiceRun_val_eq_lineFreeEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma lineChoiceRun_val_eq_lineFreeEndpoint_eq
  {n : Nat}
  {p : IsingLineBox n}
  {bs : List Bool}
-- given
  (hfree : ∀ j, j < bs.length → lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ 0 ∧ lineFreeEndpoint (p.1 : Int) (bs.take j) ≠ n) :
-- imply
  ((isingLineChoiceRun n p bs).1 : Int) = lineFreeEndpoint (p.1 : Int) bs := by
-- proof
  apply StatMech.Universality.lineChoiceRun_val_eq_lineFreeEndpoint n p bs hfree

/--
[sourceFailure_boundary_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma sourceFailure_boundary_data_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R}
  {level : Int}
  {w : IsingStoppedCouplingSourceFailureFamily R t p level}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 < level) :
-- imply
  ∃ (split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level) (j : Nat), isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level (isingLeapfrogChoiceSteps w.1.1) = some split ∧ j < split.before.length ∧ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p (w.1.1.take j)) ∧ (∀ l, l < j → ¬ isingLeapfrogBoxBoundary R (isingLeapfrogChoiceRun R p (w.1.1.take l))) ∧ (isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p) (isingLeapfrogChoiceSteps (w.1.1.take j))).1 < level ∧ isingLeapfrogBoxInt (isingLeapfrogChoiceRun R p (w.1.1.take j)) = isingDiagonalWalkEndpoint (isingLeapfrogBoxInt p) (isingLeapfrogChoiceSteps (w.1.1.take j)) := by
-- proof
  apply StatMech.Universality.sourceFailure_boundary_data R t p level hstart w

/--
[lineFreeEndpoint_choiceVertical_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma lineFreeEndpoint_choiceVertical_full_eq
  {bs : List (Bool × Bool)}
  {start : Int × Int} :
-- imply
  lineFreeEndpoint start.2 (bs.map Prod.snd) = (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 := by
-- proof
  apply StatMech.Universality.lineFreeEndpoint_choiceVertical_full bs start

/--
[lineFreeEndpoint_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma lineFreeEndpoint_translate_eq
  {bs : List Bool}
  {a b : Int} :
-- imply
  lineFreeEndpoint b bs = b + (lineFreeEndpoint a bs - a) := by
-- proof
  apply StatMech.Universality.lineFreeEndpoint_translate bs a b

/--
[exists_vertical_barrier_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma exists_vertical_barrier_prefix_eq
  {rho : Nat}
  {start : Int × Int}
  {bs : List (Bool × Bool)}
  {j : Nat}
-- given
  (hρ : 0 < rho)
  (hj : j ≤ bs.length)
  (hlower : (rho : Int) ≤ start.2)
  (hupper : start.2 + rho ≤ (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2) :
-- imply
  ∃ s, s ≤ bs.length ∧ lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 + rho := by
-- proof
  apply StatMech.Universality.exists_vertical_barrier_prefix rho hρ start bs j hj hlower hupper

/--
[exists_vertical_barrier_prefix_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma exists_vertical_barrier_prefix_lower_eq
  {rho : Nat}
  {start : Int × Int}
  {bs : List (Bool × Bool)}
-- given
  (hρ : 0 < rho)
  (hlower : (rho : Int) ≤ start.2)
  (hend : (isingDiagonalWalkEndpoint start (isingLeapfrogChoiceSteps bs)).2 ≤ start.2 - rho) :
-- imply
  ∃ s, s ≤ bs.length ∧ lineFreeEndpoint start.2 ((bs.take s).map Prod.snd) = start.2 - rho := by
-- proof
  apply StatMech.Universality.exists_vertical_barrier_prefix_lower rho hρ start bs hlower hend

/--
[transverseWitness_of_barrier_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma transverseWitness_of_barrier_exists_eq
  {rho t : Nat}
  {level : Int}
  {start : Int × Int}
  {w : IsingLeapfrogChoiceStringFamily t}
  {split : IsingDiagonalWalkHitSplit start level}
  {j : Nat}
-- given
  (hρ : 0 < rho)
  (hstart : start.1 = level - 1)
  (hsplit : isingDiagonalWalkFirstHitSplit? start level (isingLeapfrogChoiceSteps w.1) = some split)
  (hj : j < split.before.length)
  (hex : ∃ s, s ≤ j ∧ (lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 - rho ∨ lineFreeEndpoint start.2 ((w.1.take s).map Prod.snd) = start.2 + rho)) :
-- imply
  ∃ z : IsingTransverseRaceWitnessFamily rho t level, transverseRaceWitnessValue rho t level z = w /\ (z.1 : Nat) <= j := by
-- proof
  apply StatMech.Universality.transverseWitness_of_barrier_exists rho t level hρ start hstart w split hsplit j hj hex

/--
[sourceFailure_horizontal_or_transverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma sourceFailure_horizontal_or_transverse_eq
  {R level rho t : Nat}
  {p : IsingLeapfrogBox R}
  {w : IsingStoppedCouplingSourceFailureFamily R t p (level : Int)}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hlevel : 0 < level)
  (hlevelR : level < R)
  (hρ : 0 < rho)
  (hbottom : rho ≤ p.2.1)
  (htop : p.2.1 + rho ≤ R) :
-- imply
  (∃ z : IsingLeapfrogHorizontalEscapeFamily level t, z.1 = w.1) ∨ ∃ z : IsingTransverseRaceWitnessFamily rho t (level : Int), transverseRaceWitnessValue rho t (level : Int) z = w.1 := by
-- proof
  apply StatMech.Universality.sourceFailure_horizontal_or_transverse R level rho t p hstart hlevel hlevelR hρ hbottom htop w

/--
[natCard_sourceFailure_le_horizontal_add_transverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma natCard_sourceFailure_le_horizontal_add_transverse_eq
  {R level rho t : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hlevel : 0 < level)
  (hlevelR : level < R)
  (hρ : 0 < rho)
  (hbottom : rho ≤ p.2.1)
  (htop : p.2.1 + rho ≤ R) :
-- imply
  Nat.card (IsingStoppedCouplingSourceFailureFamily R t p (level : Int)) ≤ Nat.card (IsingLeapfrogHorizontalEscapeFamily level t) + Nat.card (IsingTransverseRaceWitnessFamily rho t (level : Int)) := by
-- proof
  apply StatMech.Universality.natCard_sourceFailure_le_horizontal_add_transverse R level rho t p hstart hlevel hlevelR hρ hbottom htop

/--
[sourceFailure_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma sourceFailure_diffusive_weight_le_eq
  {R level rho : Nat}
  {p : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hρ : 0 < rho)
  (hleft : rho ≤ level)
  (hright : level < R)
  (hbottom : rho ≤ p.2.1)
  (htop : p.2.1 + rho ≤ R) :
-- imply
  Nat.card (IsingStoppedCouplingSourceFailureFamily R (rho * rho) p (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
-- proof
  apply StatMech.Universality.sourceFailure_diffusive_weight_le R level rho p hstart hρ hleft hright hbottom htop

/--
[choiceRun_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma choiceRun_reflectX_eq
  {R : Nat}
  {p : IsingLeapfrogBox R}
  {bs : List (Bool × Bool)} :
-- imply
  isingLeapfrogChoiceRun R (isingLeapfrogBoxReflectX R p) (isingLeapfrogFlipXChoices bs) = isingLeapfrogBoxReflectX R (isingLeapfrogChoiceRun R p bs) := by
-- proof
  apply StatMech.Universality.choiceRun_reflectX R p bs

/--
[boxInt_reflectX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma boxInt_reflectX_eq
  {R : Nat}
  {p : IsingLeapfrogBox R} :
-- imply
  isingLeapfrogBoxInt (isingLeapfrogBoxReflectX R p) = ((R : Int) - (isingLeapfrogBoxInt p).1, (isingLeapfrogBoxInt p).2) := by
-- proof
  apply StatMech.Universality.boxInt_reflectX R p

/--
[sourceFailureReflectX_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma sourceFailureReflectX_injective_eq
  {R t : Nat}
  {p : IsingLeapfrogBox R}
  {level : Nat}
-- given
  (hlevelR : level ≤ R) :
-- imply
  Function.Injective (sourceFailureReflectX R t p level hlevelR) := by
-- proof
  apply StatMech.Universality.sourceFailureReflectX_injective R t p level hlevelR

/--
[mirrorFailureToSource_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma mirrorFailureToSource_injective_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint level (isingLeapfrogBoxInt p)) :
-- imply
  Function.Injective (mirrorFailureToSource R t p p' level hmirror) := by
-- proof
  apply StatMech.Universality.mirrorFailureToSource_injective R t p p' level hmirror

/--
[mirrorFailureReflectX_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma mirrorFailureReflectX_injective_eq
  {R t level : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hlevelR : level ≤ R) :
-- imply
  Function.Injective (mirrorFailureReflectX R t level p p' hmirror hlevelR) := by
-- proof
  apply StatMech.Universality.mirrorFailureReflectX_injective R t level p p' hmirror hlevelR

/--
[mirrorFailure_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma mirrorFailure_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hlevel : 0 < level)
  (hright : level + rho ≤ R)
  (hbottom : rho ≤ p'.2.1)
  (htop : p'.2.1 + rho ≤ R) :
-- imply
  Nat.card (IsingStoppedCouplingMirrorFailureFamily R (rho * rho) p p' (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 17 / (rho : Real) := by
-- proof
  apply StatMech.Universality.mirrorFailure_diffusive_weight_le R level rho p p' hstart hmirror hρ hlevel hright hbottom htop

/--
[stoppedCouplingBad_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma stoppedCouplingBad_diffusive_weight_le_eq
  {R level rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho ≤ level)
  (hright : level + rho ≤ R)
  (hbottom : rho ≤ p.2.1)
  (htop : p.2.1 + rho ≤ R) :
-- imply
  Nat.card (IsingLeapfrogStoppedCouplingBadFamily R (rho * rho) p p' (level : Int)) / (4 : Real) ^ (rho * rho) ≤ 38 / (rho : Real) := by
-- proof
  apply StatMech.Universality.stoppedCouplingBad_diffusive_weight_le R level rho p p' hstart hmirror hρ hleft hright hbottom htop

/--
[isingLeapfrogStoppedKernel_reflectionCoupling_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectionCoupling_l1_le_eq
  {R t : Nat}
  {p p' : IsingLeapfrogBox R}
  {level : Int} :
-- imply
  ∑ q : IsingLeapfrogBox R, := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectionCoupling_l1_le R t p p' level

/--
[isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean)
-/
@[path]
private lemma isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le_eq
  {R level rho : Nat}
  {p p' : IsingLeapfrogBox R}
-- given
  (hstart : (isingLeapfrogBoxInt p).1 + 1 = level)
  (hmirror : isingLeapfrogBoxInt p' = reflectedEndpoint (level : Int) (isingLeapfrogBoxInt p))
  (hρ : 0 < rho)
  (hleft : rho ≤ level)
  (hright : level + rho ≤ R)
  (hbottom : rho ≤ p.2.1)
  (htop : p.2.1 + rho ≤ R) :
-- imply
  (∑ q : IsingLeapfrogBox R, |isingLeapfrogStoppedKernel R (rho * rho) p q - isingLeapfrogStoppedKernel R (rho * rho) p' q|) ≤ 76 / (rho : Real) := by
-- proof
  apply StatMech.Universality.isingLeapfrogStoppedKernel_reflectedStart_diffusive_l1_le R level rho p p' hstart hmirror hρ hleft hright hbottom htop


-- created on 2026-10-23

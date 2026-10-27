import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part3
open Finset StatMech StatMech.Walls


/--
[rc63_dn_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_dn_eq_eq
  {n : ℕ}
  {i : Fin n}
  {𝒜 : Finset (Finset (Fin n))} :
-- imply
  rc63_dn i 𝒜 = rc61_dnA i 𝒜 := by
-- proof
  apply StatMech.Walls.rc63_dn_eq i 𝒜

/--
[rc63_reflInter_downdown_noninc_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_reflInter_downdown_noninc_fin2_eq
  {n : ℕ} :
-- imply
  ∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_reflInterComp 2 (rc63_dn 0 𝒜) (rc63_dn 0 ℬ)).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc63_reflInter_downdown_noninc_fin2

/--
[rc63_box_downdown_decreases_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_box_downdown_decreases_witness_eq
  {n : ℕ} :
-- imply
  (rc20_famCylBoxComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card < (rc20_famCylBoxComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card ∧ (rc20_reflInterComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card = (rc20_reflInterComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card := by
-- proof
  apply StatMech.Walls.rc63_box_downdown_decreases_witness

/--
[rc63_downdown_not_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_downdown_not_good_eq
  {n : ℕ} :
-- imply
  rc63_opGood (Down.compression 0) (Down.compression 0) = false := by
-- proof
  apply StatMech.Walls.rc63_downdown_not_good

/--
[rc63_no_opposite_compression_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_no_opposite_compression_fin2_eq
  {n : ℕ} :
-- imply
  ∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false := by
-- proof
  apply StatMech.Walls.rc63_no_opposite_compression_fin2

/--
[rc63_identity_not_injection_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_identity_not_injection_fin2_eq
  {n : ℕ} :
-- imply
  (∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}} := by
-- proof
  apply StatMech.Walls.rc63_identity_not_injection_fin2

/--
[rc63_no_coordinatewise_injection_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_no_coordinatewise_injection_fin2_eq
  {n : ℕ} :
-- imply
  rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {∅} ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} = {{0}} ∧ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {{0}} ∧ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {{0}, {0, 1}} = {∅} := by
-- proof
  apply StatMech.Walls.rc63_no_coordinatewise_injection_fin2

/--
[rc63_fixpoint_wall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_fixpoint_wall_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin 2))}
-- given
  (hd : rc62_isDown 2 𝒜 = true)
  (hu : rc62_isUp 2 ℬ = true) :
-- imply
  (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc63_fixpoint_wall 𝒜 ℬ hd hu

/--
[rc63_reimerWprobCore_of_boxUnionBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_reimerWprobCore_of_boxUnionBound_eq
  {n : ℕ}
-- given
  (h : rc60_BoxUnionBound) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.Walls.rc63_reimerWprobCore_of_boxUnionBound h

/--
[rc63_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean)
-/
@[path]
private lemma rc63_status_eq
  {n : ℕ} :
-- imply
  (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), (rc20_reflInterComp 2 (rc63_dn 0 𝒜) (rc63_dn 0 ℬ)).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧ ((rc20_famCylBoxComp 2 (rc63_dn 0 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))) (rc63_dn 0 {∅, {0}, {0, 1}})).card < (rc20_famCylBoxComp 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2))) {∅, {0}, {0, 1}}).card) ∧ (∀ p ∈ rc63_nontrivialPairs, rc63_opGood p.1 p.2 = false) ∧ ((∅ : Finset (Fin 2)) ∈ rc20_famCylBoxComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}} ∧ (∅ : Finset (Fin 2)) ∉ rc20_reflInterComp 2 ({∅, {0}} : Finset (Finset (Fin 2))) {∅, {1}}) ∧ (∀ 𝒜 ℬ : Finset (Finset (Fin 2)), rc62_isDown 2 𝒜 = true → rc62_isUp 2 ℬ = true → (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc63_status


-- created on 2026-10-23

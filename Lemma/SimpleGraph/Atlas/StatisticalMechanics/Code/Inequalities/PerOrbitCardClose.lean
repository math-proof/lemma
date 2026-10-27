import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part8
open Finset MeasureTheory StatMech


/--
[poc_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_snd_eq_eq
  [Fintype α]
  [DecidableEq α]
  {p : ConfigSpace α × ConfigSpace α}
  {k : ConfigSpace α × ConfigSpace α}
-- given
  (hk : orbitKey p = k) :
-- imply
  p.2 = poc_keyFlip k p.1 := by
-- proof
  apply StatMech.poc_snd_eq p k hk

/--
[poc_card_boxOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_card_boxOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  #(boxOrbit A B k) = #(poc_slabBox A B k) := by
-- proof
  apply StatMech.poc_card_boxOrbit A B k

/--
[poc_card_imgOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_card_imgOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {k : ConfigSpace α × ConfigSpace α} :
-- imply
  #(imgOrbit A B k) = #(poc_slabImg A B k) := by
-- proof
  apply StatMech.poc_card_imgOrbit A B k

/--
[poc_perOrbitCard_iff_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_perOrbitCard_iff_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  PerOrbitCard A B ↔ poc_SlabCard A B := by
-- proof
  apply StatMech.poc_perOrbitCard_iff_slabCard A B

/--
[poc_keyFlip_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_keyFlip_top_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω = fun a => !ω a := by
-- proof
  apply StatMech.poc_keyFlip_top ω

/--
[poc_orbitKey_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_orbitKey_top_eq
  [Fintype α]
  [DecidableEq α]
  {ω : ConfigSpace α} :
-- imply
  orbitKey (ω, poc_keyFlip (poc_topKey : ConfigSpace α × ConfigSpace α) ω) = poc_topKey := by
-- proof
  apply StatMech.poc_orbitKey_top ω

/--
[poc_slabBox_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabBox_top_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabBox A B (poc_topKey) = Finset.univ.filter (fun ω => ω ∈ disjointOccurrence A B) := by
-- proof
  apply StatMech.poc_slabBox_top A B

/--
[poc_slabImg_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabImg_top_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  poc_slabImg A B (poc_topKey) = Finset.univ.filter (fun ω => ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
-- proof
  apply StatMech.poc_slabImg_top A B

/--
[poc_slabCard_top_iff_reimerCardForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabCard_top_iff_reimerCardForm_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  #(poc_slabBox A B poc_topKey) ≤ #(poc_slabImg A B poc_topKey) ↔ poc_ReimerCardForm A B := by
-- proof
  apply StatMech.poc_slabCard_top_iff_reimerCardForm A B

/--
[poc_reimerCardForm_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_reimerCardForm_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_SlabCard A B) :
-- imply
  poc_ReimerCardForm A B := by
-- proof
  apply StatMech.poc_reimerCardForm_of_slabCard A B h

/--
[poc_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_membership_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {ω τ : ConfigSpace α}
  {wK : α → Bool}
  {wL : α → Bool}
-- given
  (hA : OccursOn A {a | wK a = true} ω)
  (hB : OccursOn B {a | wL a = true} ω)
  (hdis : ∀ a, wK a = true → wL a = false) :
-- imply
  swapGlue (fun a => !wK a) ω τ ∈ A ∧ swapGlue (fun a => !wK a) τ ω ∈ B := by
-- proof
  apply StatMech.poc_membership A B ω τ wK hA wL hB hdis

/--
[poc_swapInjection_of_witnessInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_swapInjection_of_witnessInjection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (h : poc_WitnessInjection A B) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.poc_swapInjection_of_witnessInjection A B h

/--
[poc_rbi_Bwit_FF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_rbi_Bwit_FF_eq
  [Fintype α]
  [DecidableEq α]
  {wL : Fin 2 → Bool}
-- given
  (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false false)) :
-- imply
  wL 0 = true := by
-- proof
  apply StatMech.poc_rbi_Bwit_FF wL hB

/--
[poc_rbi_Bwit_FT](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_rbi_Bwit_FT_eq
  [Fintype α]
  [DecidableEq α]
  {wL : Fin 2 → Bool}
-- given
  (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false true))
  (h0 : wL 0 = false) :
-- imply
  wL 1 = true := by
-- proof
  apply StatMech.poc_rbi_Bwit_FT wL hB h0

/--
[poc_rbi_Awit_FF_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_rbi_Awit_FF_one_eq
  [Fintype α]
  [DecidableEq α]
  {wK : Fin 2 → Bool}
-- given
  (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false false))
  (h0 : wK 0 = false) :
-- imply
  wK 1 = true := by
-- proof
  apply StatMech.poc_rbi_Awit_FF_one wK hA h0

/--
[poc_rbi_Awit_FT_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_rbi_Awit_FT_zero_eq
  [Fintype α]
  [DecidableEq α]
  {wK : Fin 2 → Bool}
-- given
  (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false true)) :
-- imply
  wK 0 = true := by
-- proof
  apply StatMech.poc_rbi_Awit_FT_zero wK hA

/--
[poc_witnessInjection_rbi_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_witnessInjection_rbi_false_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ poc_WitnessInjection rbi_A rbi_B := by
-- proof
  apply StatMech.poc_witnessInjection_rbi_false

/--
[poc_slabCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.poc_slabCard_of_disjoint_support hA hB hST

/--
[poc_slabCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  poc_SlabCard A B := by
-- proof
  apply StatMech.poc_slabCard_of_box_empty hbox

/--
[poc_slabCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_slabCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_SlabCard rbi_A rbi_B := by
-- proof
  apply StatMech.poc_slabCard_rbi

/--
[poc_reimerCardForm_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma poc_reimerCardForm_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  poc_ReimerCardForm rbi_A rbi_B := by
-- proof
  apply StatMech.poc_reimerCardForm_rbi

/--
[reimer_wprob_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma reimer_wprob_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (h : poc_SlabCard A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_of_slabCard φ hφ0 hφ1 h

/--
[reimer_wprob_core_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma reimer_wprob_core_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : poc_SlabCardAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.reimer_wprob_core_of_slabCard h

/--
[reimer_inequality_of_slabCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean)
-/
@[path]
private lemma reimer_inequality_of_slabCard_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : poc_SlabCardAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_inequality_of_slabCard h hp A B


-- created on 2026-10-23

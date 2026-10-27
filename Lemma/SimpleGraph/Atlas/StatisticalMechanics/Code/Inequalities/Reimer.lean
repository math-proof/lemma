import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
open MeasureTheory Finset StatMech


/--
[reimer_wprob_general_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma reimer_wprob_general_of_core_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (h : ReimerWprobCore)
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_general_of_core h φ hφ0 hφ1 A B

/--
[reimer_inequality_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma reimer_inequality_of_core_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : ReimerWprobCore)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_inequality_of_core h hp A B

/--
[reimer_wprob_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma reimer_wprob_zero_eq
  {φ : Fin 0 → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin 0))} :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_zero φ A B

/--
[reimerCore_holds_on_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma reimerCore_holds_on_increasing_eq
  {n : ℕ}
  {φ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimerCore_holds_on_increasing n φ hφ0 hφ1 A B hA hB

/--
[flipCfg_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma flipCfg_apply_eq
  {ω : ConfigSpace E}
  {x : E} :
-- imply
  flipCfg ω x = !(ω x) := by
-- proof
  apply StatMech.flipCfg_apply ω x

/--
[flipCfg_flipCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma flipCfg_flipCfg_eq
  {ω : ConfigSpace E} :
-- imply
  flipCfg (flipCfg ω) = ω := by
-- proof
  apply StatMech.flipCfg_flipCfg ω

/--
[flipEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma flipEquiv_apply_eq
  {ω : ConfigSpace E} :
-- imply
  flipEquiv ω = flipCfg ω := by
-- proof
  apply StatMech.flipEquiv_apply ω

/--
[flipCfg_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma flipCfg_antitone_eq
  {ω ω' : ConfigSpace E}
-- given
  (h : ω ≤ ω') :
-- imply
  flipCfg ω' ≤ flipCfg ω := by
-- proof
  apply StatMech.flipCfg_antitone h

/--
[isIncreasing_flip_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma isIncreasing_flip_preimage_eq
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsDecreasing A) :
-- imply
  IsIncreasing (flipCfg ⁻¹' A) := by
-- proof
  apply StatMech.isIncreasing_flip_preimage hA

/--
[agreeOn_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma agreeOn_flip_eq
  {K : Set E}
  {ω ω' : ConfigSpace E}
-- given
  (h : agreeOn K ω ω') :
-- imply
  agreeOn K (flipCfg ω) (flipCfg ω') := by
-- proof
  apply StatMech.agreeOn_flip h

/--
[occursOn_flip_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma occursOn_flip_preimage_eq
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {ω : ConfigSpace E} :
-- imply
  OccursOn (flipCfg ⁻¹' A) K ω ↔ OccursOn A K (flipCfg ω) := by
-- proof
  apply StatMech.occursOn_flip_preimage A K ω

/--
[preimage_flip_disjointOccurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma preimage_flip_disjointOccurrence_eq
  {A B : Set (ConfigSpace E)} :
-- imply
  flipCfg ⁻¹' (disjointOccurrence A B) = disjointOccurrence (flipCfg ⁻¹' A) (flipCfg ⁻¹' B) := by
-- proof
  apply StatMech.preimage_flip_disjointOccurrence A B

/--
[pweight_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma pweight_flip_eq
  [Fintype E]
  {φ : E → Bool → ℝ}
  {ω : ConfigSpace E} :
-- imply
  pweight φ (flipCfg ω) = pweight (fun x b => φ x (!b)) ω := by
-- proof
  apply StatMech.pweight_flip φ ω

/--
[wprob_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma wprob_flip_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {S : Set (ConfigSpace E)} :
-- imply
  wprob (fun x b => φ x (!b)) S = wprob φ (flipCfg ⁻¹' S) := by
-- proof
  apply StatMech.wprob_flip φ S

/--
[bk_wprob_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma bk_wprob_decreasing_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.bk_wprob_decreasing φ hφ0 hφ1 hA hB

/--
[bk_inequality_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer.lean)
-/
@[path]
private lemma bk_inequality_decreasing_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.bk_inequality_decreasing hp hA hB


-- created on 2026-10-23

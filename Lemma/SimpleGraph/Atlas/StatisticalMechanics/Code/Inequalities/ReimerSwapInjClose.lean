import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose
open Finset MeasureTheory StatMech


/--
[sameOrbit_iff_orbitKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma sameOrbit_iff_orbitKey_eq
  [Fintype α]
  [DecidableEq α]
  {p q : ConfigSpace α × ConfigSpace α} :
-- imply
  sameOrbit p q ↔ orbitKey p = orbitKey q := by
-- proof
  apply StatMech.sameOrbit_iff_orbitKey p q

/--
[orbitKey_swapPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma orbitKey_swapPair_eq
  [Fintype α]
  [DecidableEq α]
  {σ : ConfigSpace α × ConfigSpace α → (α → Bool)}
  {p : ConfigSpace α × ConfigSpace α} :
-- imply
  orbitKey (swapPair σ p) = orbitKey p := by
-- proof
  apply StatMech.orbitKey_swapPair σ p

/--
[swapPair_eq_of_sameOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma swapPair_eq_of_sameOrbit_eq
  [Fintype α]
  [DecidableEq α]
  {p q : ConfigSpace α × ConfigSpace α}
-- given
  (h : sameOrbit p q) :
-- imply
  q = swapPair (fun _ => fun a => decide (q.1 a ≠ p.1 a)) p := by
-- proof
  apply StatMech.swapPair_eq_of_sameOrbit p q h

/--
[r2k_swapInjection_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma r2k_swapInjection_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hpo : PerOrbitCard A B) :
-- imply
  r2k_SwapInjection A B := by
-- proof
  apply StatMech.r2k_swapInjection_of_perOrbitCard A B hpo

/--
[perOrbitCard_of_swapInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma perOrbitCard_of_swapInjection_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hSI : r2k_SwapInjection A B) :
-- imply
  PerOrbitCard A B := by
-- proof
  apply StatMech.perOrbitCard_of_swapInjection A B hSI

/--
[r2k_swapInjection_iff_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma r2k_swapInjection_iff_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)} :
-- imply
  r2k_SwapInjection A B ↔ PerOrbitCard A B := by
-- proof
  apply StatMech.r2k_swapInjection_iff_perOrbitCard A B

/--
[reimer_wprob_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma reimer_wprob_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  {φ : α → Bool → ℝ}
  {A B : Set (ConfigSpace α)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hpo : PerOrbitCard A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_of_perOrbitCard φ hφ0 hφ1 hpo

/--
[perOrbitCard_of_disjoint_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma perOrbitCard_of_disjoint_support_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
  {S T : Finset α}
-- given
  (hA : DependsOn A (↑S))
  (hB : DependsOn B (↑T))
  (hST : Disjoint S T) :
-- imply
  PerOrbitCard A B := by
-- proof
  apply StatMech.perOrbitCard_of_disjoint_support hA hB hST

/--
[perOrbitCard_of_box_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma perOrbitCard_of_box_empty_eq
  [Fintype α]
  [DecidableEq α]
  {A B : Set (ConfigSpace α)}
-- given
  (hbox : disjointOccurrence A B = ∅) :
-- imply
  PerOrbitCard A B := by
-- proof
  apply StatMech.perOrbitCard_of_box_empty hbox

/--
[perOrbitCard_rbi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma perOrbitCard_rbi_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  PerOrbitCard rbi_A rbi_B := by
-- proof
  apply StatMech.perOrbitCard_rbi

/--
[reimer_wprob_core_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma reimer_wprob_core_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : PerOrbitCardAll) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.reimer_wprob_core_of_perOrbitCard h

/--
[reimer_inequality_of_perOrbitCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerSwapInjClose.lean)
-/
@[path]
private lemma reimer_inequality_of_perOrbitCard_eq
  [Fintype α]
  [DecidableEq α]
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (h : PerOrbitCardAll)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_inequality_of_perOrbitCard h hp A B


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
open Finset StatMech


/--
[downComp_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma downComp_nonMemberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).nonMemberSubfamily i = 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.downComp_nonMemberSubfamily i 𝒜

/--
[downComp_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma downComp_memberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).memberSubfamily i = 𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.downComp_memberSubfamily i 𝒜

/--
[dpairsCount_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_double_sum_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, (if Disjoint S T then 1 else 0) := by
-- proof
  apply StatMech.dpairsCount_double_sum 𝒜 ℬ

/--
[dpairsCount_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_mono_left_eq
  [DecidableEq α]
  {𝒜 𝒜' : Finset (Finset α)}
  {ℬ : Finset (Finset α)}
-- given
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
-- proof
  apply StatMech.dpairsCount_mono_left ℬ h

/--
[dpairsCount_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_mono_right_eq
  [DecidableEq α]
  {𝒞 : Finset (Finset α)}
  {ℬ ℬ' : Finset (Finset α)}
-- given
  (h : ℬ ⊆ ℬ') :
-- imply
  dpairsCount 𝒞 ℬ ≤ dpairsCount 𝒞 ℬ' := by
-- proof
  apply StatMech.dpairsCount_mono_right 𝒞 h

/--
[dpairsCount_modular_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_modular_left_eq
  [DecidableEq α]
  {𝒜 ℬ 𝒞 : Finset (Finset α)} :
-- imply
  dpairsCount (𝒜 ∪ ℬ) 𝒞 + dpairsCount (𝒜 ∩ ℬ) 𝒞 = dpairsCount 𝒜 𝒞 + dpairsCount ℬ 𝒞 := by
-- proof
  apply StatMech.dpairsCount_modular_left 𝒜 ℬ 𝒞

/--
[dpairsCount_modular_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_modular_right_eq
  [DecidableEq α]
  {𝒜 ℬ 𝒞 : Finset (Finset α)} :
-- imply
  dpairsCount 𝒞 (𝒜 ∪ ℬ) + dpairsCount 𝒞 (𝒜 ∩ ℬ) = dpairsCount 𝒞 𝒜 + dpairsCount 𝒞 ℬ := by
-- proof
  apply StatMech.dpairsCount_modular_right 𝒜 ℬ 𝒞

/--
[dpairsCount_fiber_downDown_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_fiber_downDown_ineq_eq
  [DecidableEq α]
  {am an bm bn : Finset (Finset α)} :
-- imply
  dpairsCount an bn + dpairsCount am bn + dpairsCount an bm ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn) + dpairsCount (am ∪ an) (bm ∩ bn) := by
-- proof
  apply StatMech.dpairsCount_fiber_downDown_ineq am an bm bn

/--
[dpairsCount_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma dpairsCount_downDown_mono_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.dpairsCount_downDown_mono 𝒜 ℬ i

/--
[wdpairs'_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_double_sum_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  wdpairs' w i 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, pairKernel' w i S T := by
-- proof
  apply StatMech.wdpairs'_double_sum w i 𝒜 ℬ

/--
[pairKernel'_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma pairKernel'_nonneg_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {S T : Finset α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  0 ≤ pairKernel' w i S T := by
-- proof
  apply StatMech.pairKernel'_nonneg hw i S T

/--
[wdpairs'_mono_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_mono_left_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 𝒜' : Finset (Finset α)}
  {ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (h : 𝒜 ⊆ 𝒜') :
-- imply
  wdpairs' w i 𝒜 ℬ ≤ wdpairs' w i 𝒜' ℬ := by
-- proof
  apply StatMech.wdpairs'_mono_left hw i ℬ h

/--
[wdpairs'_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_mono_right_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒞 : Finset (Finset α)}
  {ℬ ℬ' : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (h : ℬ ⊆ ℬ') :
-- imply
  wdpairs' w i 𝒞 ℬ ≤ wdpairs' w i 𝒞 ℬ' := by
-- proof
  apply StatMech.wdpairs'_mono_right hw i 𝒞 h

/--
[wdpairs'_modular_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_modular_left_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ 𝒞 : Finset (Finset α)} :
-- imply
  wdpairs' w i (𝒜 ∪ ℬ) 𝒞 + wdpairs' w i (𝒜 ∩ ℬ) 𝒞 = wdpairs' w i 𝒜 𝒞 + wdpairs' w i ℬ 𝒞 := by
-- proof
  apply StatMech.wdpairs'_modular_left w i 𝒜 ℬ 𝒞

/--
[wdpairs'_modular_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_modular_right_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ 𝒞 : Finset (Finset α)} :
-- imply
  wdpairs' w i 𝒞 (𝒜 ∪ ℬ) + wdpairs' w i 𝒞 (𝒜 ∩ ℬ) = wdpairs' w i 𝒞 𝒜 + wdpairs' w i 𝒞 ℬ := by
-- proof
  apply StatMech.wdpairs'_modular_right w i 𝒜 ℬ 𝒞

/--
[wdpairs'_fiber_downDown_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs'_fiber_downDown_ineq_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {am an bm bn : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : w i true ≤ w i false) :
-- imply
  w i false * w i false * wdpairs' w i an bn + w i true * w i false * wdpairs' w i am bn + w i false * w i true * wdpairs' w i an bm ≤ w i false * w i false * wdpairs' w i (am ∪ an) (bm ∪ bn) + w i true * w i false * wdpairs' w i (am ∩ an) (bm ∪ bn) + w i false * w i true * wdpairs' w i (am ∪ an) (bm ∩ bn) := by
-- proof
  apply StatMech.wdpairs'_fiber_downDown_ineq hw i hdom am an bm bn

/--
[wdpairs_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs_downDown_mono_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b)
  (hdom : w i true ≤ w i false) :
-- imply
  wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.wdpairs_downDown_mono hw i hdom 𝒜 ℬ

/--
[wdpairs_downDown_mono_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs_downDown_mono_satisfiable_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  wdpairs (fun (_ : Fin 1) b => if b then (0 : ℝ) else 1) ({{0}} : Finset (Finset (Fin 1))) {{0}} ≤ wdpairs (fun (_ : Fin 1) b => if b then (0 : ℝ) else 1) (Down.compression 0 ({{0}} : Finset (Finset (Fin 1)))) (Down.compression 0 ({{0}} : Finset (Finset (Fin 1)))) := by
-- proof
  apply StatMech.wdpairs_downDown_mono_satisfiable

/--
[wdpairs_downDown_not_mono_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs_downDown_not_mono_general_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  ∃ (w : Fin 1 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1), (∀ x b, 0 ≤ w x b) ∧ ¬ (wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ)) := by
-- proof
  apply StatMech.wdpairs_downDown_not_mono_general

/--
[wdpairs_symm_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma wdpairs_symm_downDown_mono_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.wdpairs_symm_downDown_mono hsym i 𝒜 ℬ

/--
[fmarg_symm_downComp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean)
-/
@[path]
private lemma fmarg_symm_downComp_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fmarg w (Down.compression i 𝒜) = fmarg w 𝒜 := by
-- proof
  apply StatMech.fmarg_symm_downComp hsym i 𝒜


-- created on 2026-10-23

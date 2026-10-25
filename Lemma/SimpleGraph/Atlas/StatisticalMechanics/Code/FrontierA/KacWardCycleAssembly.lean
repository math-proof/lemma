import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly.Part3
open Finset StatMech StatMech.FrontierA


/--
[kw_perm_eq_one_or_inv_of_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kw_perm_eq_one_or_inv_of_cycle_eq
  [Finite E]
  [Nonempty E]
  {sigma tau : Equiv.Perm E}
-- given
  (hcycle : sigma.IsCycle)
  (hfree : ∀ i, sigma i ≠ i)
  (hchoice : ∀ i, tau i = i ∨ tau i = sigma⁻¹ i) :
-- imply
  tau = 1 ∨ tau = sigma⁻¹ := by
-- proof
  apply StatMech.FrontierA.kw_perm_eq_one_or_inv_of_cycle sigma tau hcycle hfree hchoice

/--
[kw_one_sub_weightedCycle_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kw_one_sub_weightedCycle_apply_eq
  [Fintype E]
  [DecidableEq E]
  {sigma tau : Equiv.Perm E}
  {i : E}
-- given
  (weight : E -> ℂ)
  (hfree : ∀ i, sigma i ≠ i) :
-- imply
  (1 - kwWeightedCycleTransition sigma weight) (tau i) i = if tau i = i then 1 else if tau i = sigma⁻¹ i then -weight (sigma⁻¹ i) else 0 := by
-- proof
  apply StatMech.FrontierA.kw_one_sub_weightedCycle_apply sigma tau weight hfree i

/--
[kw_det_one_sub_weightedCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kw_det_one_sub_weightedCycle_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {sigma : Equiv.Perm E}
-- given
  (weight : E -> ℂ)
  (hcycle : sigma.IsCycle)
  (hfree : ∀ i, sigma i ≠ i) :
-- imply
  (1 - kwWeightedCycleTransition sigma weight).det = 1 - ∏ i, weight i := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_weightedCycle sigma weight hcycle hfree

/--
[kw_det_twoOrientationCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kw_det_twoOrientationCycle_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {sigma : Equiv.Perm E}
-- given
  (weight : Bool -> E -> ℂ)
  (hcycle : sigma.IsCycle)
  (hfree : ∀ i, sigma i ≠ i) :
-- imply
  (1 - kwTwoOrientationCycleTransition sigma weight).det = (1 - ∏ i, weight false i) * (1 - ∏ i, weight true i) := by
-- proof
  apply StatMech.FrontierA.kw_det_twoOrientationCycle sigma weight hcycle hfree

/--
[kacWard_abstract_cycle_of_phase_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kacWard_abstract_cycle_of_phase_sign_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  {sigma : Equiv.Perm E}
-- given
  (edgeWeight : E -> ℂ)
  (phase : Bool -> E -> ℂ)
  (hcycle : sigma.IsCycle)
  (hfree : ∀ i, sigma i ≠ i)
  (hphase : ∀ b, ∏ i, phase b i = -1) :
-- imply
  (1 - kwTwoOrientationCycleTransition sigma (fun b i => edgeWeight i * phase b i)).det = (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_abstract_cycle_of_phase_sign sigma edgeWeight phase hcycle hfree hphase

/--
[kw_finRotate_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kw_finRotate_free_eq
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ∀ i : Fin n, finRotate n i ≠ i := by
-- proof
  apply StatMech.FrontierA.kw_finRotate_free hn

/--
[kacWard_rectilinear_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean)
-/
@[path]
private lemma kacWard_rectilinear_cycle_eq
  {n : ℕ}
  [NeZero n]
  {omega : ℂ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (d : Fin n -> Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hnu : ∀ i, d (i + 1) ≠ d i + 2)
  (edgeWeight : Fin n -> ℂ) :
-- imply
  (1 - kwTwoOrientationCycleTransition (finRotate n) (fun _ i => edgeWeight i * ons_turnW omega (d i) (d (i + 1)))).det = (kwAbstractCycleEvenPolynomial edgeWeight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_rectilinear_cycle omega homega hI d hclosed hsimple hn hnu edgeWeight


-- created on 2026-10-23

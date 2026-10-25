import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly.Part2
open StatMech StatMech.FrontierA


/--
[kwStrictlyForward.blockTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean)
-/
@[path]
private lemma blockTriangular_eq
  [Preorder Block]
  {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
-- given
  (hforward : kwStrictlyForward forward) :
-- imply
  forward.BlockTriangular Prod.snd := by
-- proof
  apply StatMech.FrontierA.kwStrictlyForward.blockTriangular hforward

/--
[kwStrictlyForward.eq_zero_of_same_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean)
-/
@[path]
private lemma eq_zero_of_same_block_eq
  [Preorder Block]
  {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
  {i j : (E × Bool) × Block}
-- given
  (hforward : kwStrictlyForward forward)
  (hij : i.2 = j.2) :
-- imply
  forward i j = 0 := by
-- proof
  apply StatMech.FrontierA.kwStrictlyForward.eq_zero_of_same_block hforward hij

/--
[kw_cycleFamily_diagonalBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean)
-/
@[path]
private lemma kw_cycleFamily_diagonalBlock_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype Block]
  [DecidableEq Block]
  [LinearOrder Block]
  {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
  {b : Block}
-- given
  (sigma : Block -> Equiv.Perm E)
  (weight : Block -> Bool -> E -> ℂ)
  (hforward : kwStrictlyForward forward) :
-- imply
  Matrix.reindex (kwCycleBlockEquiv b) (kwCycleBlockEquiv b) ((kwCycleFamilyExtension sigma weight forward).toSquareBlock Prod.snd b) = kwTwoOrientationCycleTransition (sigma b) (weight b) := by
-- proof
  apply StatMech.FrontierA.kw_cycleFamily_diagonalBlock sigma weight forward hforward b

/--
[kw_det_cycleFamilyExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean)
-/
@[path]
private lemma kw_det_cycleFamilyExtension_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  [Fintype Block]
  [DecidableEq Block]
  [LinearOrder Block]
  {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
-- given
  (sigma : Block -> Equiv.Perm E)
  (weight : Block -> Bool -> E -> ℂ)
  (hforward : kwStrictlyForward forward) :
-- imply
  (1 - kwCycleFamilyExtension sigma weight forward).det = ∏ b : Block, (1 - kwTwoOrientationCycleTransition (sigma b) (weight b)).det := by
-- proof
  apply StatMech.FrontierA.kw_det_cycleFamilyExtension sigma weight forward hforward

/--
[kacWard_abstract_cactus_of_phase_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCactusAssembly.lean)
-/
@[path]
private lemma kacWard_abstract_cactus_of_phase_sign_eq
  [Fintype E]
  [DecidableEq E]
  [Nonempty E]
  [Fintype Block]
  [DecidableEq Block]
  [LinearOrder Block]
  {forward : Matrix ((E × Bool) × Block) ((E × Bool) × Block) ℂ}
-- given
  (sigma : Block -> Equiv.Perm E)
  (edgeWeight : Block -> E -> ℂ)
  (phase : Block -> Bool -> E -> ℂ)
  (hforward : kwStrictlyForward forward)
  (hcycle : ∀ b, (sigma b).IsCycle)
  (hfree : ∀ b i, sigma b i ≠ i)
  (hphase : ∀ b o, ∏ i, phase b o i = -1) :
-- imply
  (1 - kwCycleFamilyExtension sigma (fun b o i => edgeWeight b i * phase b o i) forward).det = (kwAbstractCactusEvenPolynomial edgeWeight) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_abstract_cactus_of_phase_sign sigma edgeWeight phase forward hforward hcycle hfree hphase


-- created on 2026-10-23

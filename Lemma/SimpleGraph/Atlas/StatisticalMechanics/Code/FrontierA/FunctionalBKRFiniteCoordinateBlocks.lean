import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
open StatMech StatMech.FrontierA


/--
[piAgreeOn_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piAgreeOn_refl_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (x : ∀ e, S e) :
-- imply
  piAgreeOn K x x := by
-- proof
  apply StatMech.FrontierA.piAgreeOn_refl K x

/--
[mem_piAgreementFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma mem_piAgreementFiber_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {x y : ∀ e, S e} :
-- imply
  y ∈ piAgreementFiber K x ↔ piAgreeOn K x y := by
-- proof
  apply StatMech.FrontierA.mem_piAgreementFiber

/--
[piAgreementFiber_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piAgreementFiber_nonempty_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (x : ∀ e, S e) :
-- imply
  (piAgreementFiber K x).Nonempty := by
-- proof
  apply StatMech.FrontierA.piAgreementFiber_nonempty K x

/--
[wholeBlocks_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma wholeBlocks_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {K L : Set E}
-- given
  (hKL : Disjoint K L) :
-- imply
  Disjoint (wholeBlocks (D := D) K) (wholeBlocks (D := D) L) := by
-- proof
  apply StatMech.FrontierA.wholeBlocks_disjoint hKL

/--
[decodeBlockConfig_encodeBlockConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma decodeBlockConfig_encodeBlockConfig_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e) :
-- imply
  decodeBlockConfig decode (encodeBlockConfig decode hdecode x) = x := by
-- proof
  apply StatMech.FrontierA.decodeBlockConfig_encodeBlockConfig decode hdecode x

/--
[liftPiCylinder_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma liftPiCylinder_agreeOn_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e) :
-- imply
  agreeOn (wholeBlocks (D := D) K) omega (liftPiCylinder decode hdecode K omega x) := by
-- proof
  apply StatMech.FrontierA.liftPiCylinder_agreeOn decode hdecode K omega x

/--
[decodeBlockConfig_liftPiCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma decodeBlockConfig_liftPiCylinder_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e)
  (hx : piAgreeOn K (decodeBlockConfig decode omega) x) :
-- imply
  decodeBlockConfig decode (liftPiCylinder decode hdecode K omega x) = x := by
-- proof
  apply StatMech.FrontierA.decodeBlockConfig_liftPiCylinder decode hdecode K omega x hx

/--
[piAgreeOn_decode_of_agreeOn_wholeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piAgreeOn_decode_of_agreeOn_wholeBlocks_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega eta : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (h : agreeOn (wholeBlocks (D := D) K) omega eta) :
-- imply
  piAgreeOn K (decodeBlockConfig decode omega) (decodeBlockConfig decode eta) := by
-- proof
  apply StatMech.FrontierA.piAgreeOn_decode_of_agreeOn_wholeBlocks decode K h

/--
[piCylinderMin_decodeBlockConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piCylinderMin_decodeBlockConfig_eq
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {omega : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f : (∀ e, S e) → ℝ) :
-- imply
  piCylinderMin f K (decodeBlockConfig decode omega) = cylinderMin (f ∘ decodeBlockConfig decode) (wholeBlocks (D := D) K) omega := by
-- proof
  apply StatMech.FrontierA.piCylinderMin_decodeBlockConfig decode hdecode f K omega

/--
[piFunctionalDisjointMaxAt_decode_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piFunctionalDisjointMaxAt_decode_le_eq
  [Fintype E]
  [DecidableEq E]
  {omega eta : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ) :
-- imply
  piFunctionalDisjointMaxAt f g (decodeBlockConfig decode omega) (decodeBlockConfig decode eta) ≤ functionalDisjointMaxAt (f ∘ decodeBlockConfig decode) (g ∘ decodeBlockConfig decode) omega eta := by
-- proof
  apply StatMech.FrontierA.piFunctionalDisjointMaxAt_decode_le decode hdecode f g omega eta

/--
[piFunctionalDisjointMax_decode_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma piFunctionalDisjointMax_decode_le_eq
  [Fintype E]
  [DecidableEq E]
  {omega : ConfigSpace (E × D)}
-- given
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ) :
-- imply
  piFunctionalDisjointMax f g (decodeBlockConfig decode omega) ≤ functionalDisjointMax (f ∘ decodeBlockConfig decode) (g ∘ decodeBlockConfig decode) omega := by
-- proof
  apply StatMech.FrontierA.piFunctionalDisjointMax_decode_le decode hdecode f g omega

/--
[functionalBKR_finiteCoordinateBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma functionalBKR_finiteCoordinateBlocks_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E × D → Bool → ℝ}
-- given
  (hphi0 : ∀ z b, 0 ≤ phi z b)
  (hphi1 : ∀ z, phi z false + phi z true = 1)
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  blockProductExpectation phi decode (piFunctionalDisjointMax f g) ≤ blockProductExpectation phi decode f * blockProductExpectation phi decode g := by
-- proof
  apply StatMech.FrontierA.functionalBKR_finiteCoordinateBlocks phi hphi0 hphi1 decode hdecode f g hf0 hg0

/--
[dualFunctionalBKR_finiteCoordinateBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean)
-/
@[path]
private lemma dualFunctionalBKR_finiteCoordinateBlocks_eq
  [Fintype E]
  [DecidableEq E]
  {phi : E × D → Bool → ℝ}
-- given
  (hphi0 : ∀ z b, 0 ≤ phi z b)
  (hphi1 : ∀ z, phi z false + phi z true = 1)
  (decode : ∀ e, (D → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  dualProductExpectation phi (fun pair => piFunctionalDisjointMaxAt f g (decodeBlockConfig decode pair.1) (decodeBlockConfig decode pair.2)) ≤ blockProductExpectation phi decode (fun x => f x * g x) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_finiteCoordinateBlocks phi hphi0 hphi1 decode hdecode f g hf0 hg0


-- created on 2026-10-23

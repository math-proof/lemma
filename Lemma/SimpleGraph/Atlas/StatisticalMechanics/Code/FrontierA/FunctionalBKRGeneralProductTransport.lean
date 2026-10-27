import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductTransport
open MeasureTheory Set Filter Topology StatMech StatMech.FrontierA


/--
[dualProductExpectation_eq_iterated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductTransport.lean)
-/
@[path]
private lemma dualProductExpectation_eq_iterated_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  [Fintype I]
  [DecidableEq I]
  {phi : I → Bool → ℝ}
  {H : (StatMech.ConfigSpace I × StatMech.ConfigSpace I) → ℝ} :
-- imply
  dualProductExpectation phi H = productExpectation phi (fun omega => productExpectation phi (fun eta => H (omega, eta))) := by
-- proof
  apply StatMech.FrontierA.dualProductExpectation_eq_iterated phi H

/--
[productExpectation_decodeDependent_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductTransport.lean)
-/
@[path]
private lemma productExpectation_decodeDependent_point_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {phi : Sigma D → Bool → ℝ}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (w : ∀ e, S e → ℝ)
  (hexpect : ∀ e (h : S e → ℝ), productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) = ∑ s, w e s * h s)
  (x : ∀ e, S e) :
-- imply
  productExpectation phi (fun omega => if decodeDependentBlockConfig decode omega = x then 1 else 0) = ∏ e, w e (x e) := by
-- proof
  apply StatMech.FrontierA.productExpectation_decodeDependent_point phi decode w hexpect x

/--
[productExpectation_decodeDependent_eq_finitePiExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductTransport.lean)
-/
@[path]
private lemma productExpectation_decodeDependent_eq_finitePiExpectation_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {phi : Sigma D → Bool → ℝ}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (w : ∀ e, S e → ℝ)
  (hexpect : ∀ e (h : S e → ℝ), productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) = ∑ s, w e s * h s)
  (H : (∀ e, S e) → ℝ) :
-- imply
  productExpectation phi (H ∘ decodeDependentBlockConfig decode) = finitePiExpectation w H := by
-- proof
  apply StatMech.FrontierA.productExpectation_decodeDependent_eq_finitePiExpectation phi decode w hexpect H

/--
[dualProductExpectation_decodeDependent_eq_finitePiDualExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductTransport.lean)
-/
@[path]
private lemma dualProductExpectation_decodeDependent_eq_finitePiDualExpectation_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {phi : Sigma D → Bool → ℝ}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (w : ∀ e, S e → ℝ)
  (hexpect : ∀ e (h : S e → ℝ), productExpectation (fun d b => phi ⟨e, d⟩ b) (h ∘ decode e) = ∑ s, w e s * h s)
  (H : ((∀ e, S e) × (∀ e, S e)) → ℝ) :
-- imply
  dualProductExpectation phi (fun pair => H (decodeDependentBlockConfig decode pair.1, decodeDependentBlockConfig decode pair.2)) = finitePiDualExpectation w H := by
-- proof
  apply StatMech.FrontierA.dualProductExpectation_decodeDependent_eq_finitePiDualExpectation phi decode w hexpect H


-- created on 2026-10-23

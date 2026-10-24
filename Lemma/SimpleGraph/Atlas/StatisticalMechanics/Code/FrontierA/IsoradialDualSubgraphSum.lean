import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum
open StatMech StatMech.FrontierA


/--
[isoradialCriticalMu_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma isoradialCriticalMu_dual_eq
  [Fintype E]
  [DecidableEq E]
  {theta : Real} :
-- imply
  isoradialCriticalMu (Real.pi / 2 - theta) = -(isoradialCriticalMu theta)⁻¹ := by
-- proof
  apply StatMech.FrontierA.isoradialCriticalMu_dual theta

/--
[isoradialCriticalMu_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma isoradialCriticalMu_ne_zero_eq
  [Fintype E]
  [DecidableEq E]
  {theta : Real}
-- given
  (htheta : 0 < theta)
  (htheta' : theta < Real.pi / 2) :
-- imply
  isoradialCriticalMu theta ≠ 0 := by
-- proof
  apply StatMech.FrontierA.isoradialCriticalMu_ne_zero htheta htheta'

/--
[finsetComplementEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma finsetComplementEquiv_apply_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E} :
-- imply
  finsetComplementEquiv F = Fᶜ := by
-- proof
  apply StatMech.FrontierA.finsetComplementEquiv_apply F

/--
[prod_one_sub_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma prod_one_sub_inv_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {B : Finset E}
-- given
  (character : E -> K)
  (hcharacter : forall e, e ∈ B -> character e ≠ 0) :
-- imply
  (∏ e ∈ B, (1 - (character e)⁻¹)) = (-1 : K) ^ B.card * (∏ e ∈ B, character e)⁻¹ * ∏ e ∈ B, (1 - character e) := by
-- proof
  apply StatMech.FrontierA.prod_one_sub_inv character hcharacter

/--
[prod_one_sub_inv_of_prod_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma prod_one_sub_inv_of_prod_eq_one_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {B : Finset E}
-- given
  (character : E -> K)
  (hcharacter : forall e, e ∈ B -> character e ≠ 0)
  (htotal : ∏ e ∈ B, character e = 1) :
-- imply
  (∏ e ∈ B, (1 - (character e)⁻¹)) = (-1 : K) ^ B.card * ∏ e ∈ B, (1 - character e) := by
-- proof
  apply StatMech.FrontierA.prod_one_sub_inv_of_prod_eq_one character hcharacter htotal

/--
[compl_card_add_boundary_mod_two_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma compl_card_add_boundary_mod_two_constant_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (boundaryComponents : Finset E -> Nat)
  (htoggle : forall (F : Finset E) (e : E), e ∉ F -> boundaryComponents (insert e F) % 2 = (boundaryComponents F + 1) % 2) :
-- imply
  forall F : Finset E, (Fᶜ.card + boundaryComponents F) % 2 = (Fintype.card E + boundaryComponents ∅) % 2 := by
-- proof
  apply StatMech.FrontierA.compl_card_add_boundary_mod_two_constant boundaryComponents htoggle

/--
[compl_card_add_boundary_mod_two_eq_dualVertexCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma compl_card_add_boundary_mod_two_eq_dualVertexCount_eq
  [Fintype E]
  [DecidableEq E]
  {dualVertexCount : Nat}
-- given
  (boundaryComponents : Finset E -> Nat)
  (htoggle : forall (F : Finset E) (e : E), e ∉ F -> boundaryComponents (insert e F) % 2 = (boundaryComponents F + 1) % 2)
  (hbase : (Fintype.card E + boundaryComponents ∅) % 2 = dualVertexCount % 2) :
-- imply
  forall F : Finset E, (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2 := by
-- proof
  apply StatMech.FrontierA.compl_card_add_boundary_mod_two_eq_dualVertexCount boundaryComponents dualVertexCount htoggle hbase

/--
[inv_univ_prod_mul_prod_eq_compl_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma inv_univ_prod_mul_prod_eq_compl_prod_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {F : Finset E}
-- given
  (weight : E -> K)
  (hweight : forall e, weight e ≠ 0) :
-- imply
  (∏ e : E, weight e)⁻¹ * (∏ e ∈ F, weight e) = ∏ e ∈ Fᶜ, (weight e)⁻¹ := by
-- proof
  apply StatMech.FrontierA.inv_univ_prod_mul_prod_eq_compl_prod weight hweight F

/--
[kwDualSubgraphSum_complement_duality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma kwDualSubgraphSum_complement_duality_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {dualVertexCount : Nat}
-- given
  (coefficient dualCoefficient : Finset E -> K)
  (weight : E -> K)
  (hweight : forall e, weight e ≠ 0)
  (hcoefficient : forall F : Finset E, (-1 : K) ^ Fᶜ.card * dualCoefficient Fᶜ = (-1 : K) ^ dualVertexCount * coefficient F) :
-- imply
  kwDualSubgraphSum dualCoefficient (fun e => -(weight e)⁻¹) = (-1 : K) ^ dualVertexCount * ((∏ e : E, weight e)⁻¹ * kwDualSubgraphSum coefficient weight) := by
-- proof
  apply StatMech.FrontierA.kwDualSubgraphSum_complement_duality coefficient dualCoefficient weight hweight dualVertexCount hcoefficient

/--
[kwDualSubgraphSum_coefficient_sign_of_boundaryParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma kwDualSubgraphSum_coefficient_sign_of_boundaryParity_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {dualVertexCount : Nat}
-- given
  (coefficient dualCoefficient : Finset E -> K)
  (boundaryComponents : Finset E -> Nat)
  (hboundary : forall F : Finset E, dualCoefficient Fᶜ = (-1 : K) ^ boundaryComponents F * coefficient F)
  (hparity : forall F : Finset E, (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2) :
-- imply
  forall F : Finset E, (-1 : K) ^ Fᶜ.card * dualCoefficient Fᶜ = (-1 : K) ^ dualVertexCount * coefficient F := by
-- proof
  apply StatMech.FrontierA.kwDualSubgraphSum_coefficient_sign_of_boundaryParity coefficient dualCoefficient boundaryComponents dualVertexCount hboundary hparity

/--
[kwDualSubgraphSum_complement_duality_of_boundaryParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean)
-/
@[path]
private lemma kwDualSubgraphSum_complement_duality_of_boundaryParity_eq
  [Fintype E]
  [DecidableEq E]
  [Field K]
  {dualVertexCount : Nat}
-- given
  (coefficient dualCoefficient : Finset E -> K)
  (weight : E -> K)
  (hweight : forall e, weight e ≠ 0)
  (boundaryComponents : Finset E -> Nat)
  (hboundary : forall F : Finset E, dualCoefficient Fᶜ = (-1 : K) ^ boundaryComponents F * coefficient F)
  (hparity : forall F : Finset E, (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2) :
-- imply
  kwDualSubgraphSum dualCoefficient (fun e => -(weight e)⁻¹) = (-1 : K) ^ dualVertexCount * ((∏ e : E, weight e)⁻¹ * kwDualSubgraphSum coefficient weight) := by
-- proof
  apply StatMech.FrontierA.kwDualSubgraphSum_complement_duality_of_boundaryParity coefficient dualCoefficient weight hweight boundaryComponents dualVertexCount hboundary hparity


-- created on 2026-10-23

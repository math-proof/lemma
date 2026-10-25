import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.BNPair.Generalized.Theorems
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism.Part2
open GeneralizedBNPair CoxeterGroup


namespace GeneralizedBNPair

/--
[Tt_le_Bt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/TypePreserving.lean)
-/
@[path]
private lemma Tt_le_Bt
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tt ≤ gbp.Bt :=
-- proof
  gbp.Tt_eq ▸ inf_le_left

end GeneralizedBNPair

namespace CoxeterGroup

/--
[simple_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean)
Via `coxeterRepresentation_simple`: equal simple reflections give equal `sigmaLinearEquiv`, which distinguish basis vectors.
-/
@[path]
private lemma simple_injective
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {i j : B}
-- given
  (h : cs.simple i = cs.simple j) :
-- imply
  i = j := by
-- proof
  have hσ : sigmaLinearEquiv M i = sigmaLinearEquiv M j := by
    rw [← coxeterRepresentation_simple M cs i, ← coxeterRepresentation_simple M cs j, h]
  by_contra hne
  have hL : (sigmaLinearEquiv M i (e i)) i = (-1 : ℝ) := by
    rw [sigmaLinearEquiv_apply, sigma_e_self]
    simp [e, Pi.single_eq_same]
  have hR : (sigmaLinearEquiv M j (e i)) i = (1 : ℝ) := by
    rw [sigmaLinearEquiv_apply, sigma_e_other]
    simp only [e, Pi.single_eq_same]
    rw [Pi.single_eq_of_ne hne]
    ring
  have : (sigmaLinearEquiv M i (e i)) i = (sigmaLinearEquiv M j (e i)) i := by
    rw [hσ]
  linarith

end CoxeterGroup

namespace GeneralizedBNPair

/--
[Tlifted_le_Blifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma Tlifted_le_Blifted
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Blifted := by
-- proof
  unfold Tlifted Blifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_left)

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[Tlifted_le_Nlifted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma Tlifted_le_Nlifted
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Nlifted := by
-- proof
  unfold Tlifted Nlifted
  exact Subgroup.map_mono (gbp.strictBNPair.T_eq ▸ inf_le_right)

end GeneralizedBNPair

namespace GeneralizedBNPair

/--
[T_le_Tt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/BNPair/Generalized/Theorems.lean)
-/
@[path]
private lemma T_le_Tt
  [Fintype B_idx]
  [DecidableEq B_idx]
  [Group Gt]
  {M : CoxeterMatrix B_idx}
  {gbp : GeneralizedBNPair Gt M} :
-- imply
  gbp.Tlifted ≤ gbp.Tt :=
-- proof
  gbp.Tt_eq ▸ le_inf
    (le_trans Tlifted_le_Blifted gbp.B_le_Bt)
    (le_trans Tlifted_le_Nlifted gbp.N_le_Nt)

end GeneralizedBNPair


-- created on 2026-10-23
-- updated on 2026-10-24

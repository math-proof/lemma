-- Carved from Lemma/Definitions/Def_GaloisRep_CompletionBridge.lean: instance decls only.
import Mathlib
import Def.FLTPrelim_Ramification
import Lemma.GaloisRep.CompletionBridge

set_option autoImplicit false

open scoped NNReal Pointwise

local instance isAlgebraicQbar_cb : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_cb : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_cb : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

variable (q : ℕ) [Fact q.Prime]

section Galois

noncomputable local instance instAlgebraQbarPadic : Algebra (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  (padicEmbedding q).toRingHom.toAlgebra
local instance instTowerQbarPadic :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
local instance instTowerQqPadic : IsScalarTower ℚ ℚ_[q] (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

end Galois

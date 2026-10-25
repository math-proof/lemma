-- Carved from Lemma/Definitions/Def_GaloisRep_ComplexConjugation.lean: instance decls only.
import Mathlib
import Lemma.GaloisRep.ComplexConjugation

set_option autoImplicit false

local instance isAlgebraicQbar_cc : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_cc : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
local instance normalQbar_cc : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
noncomputable local instance instDecEqQbar_cc : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable local instance instAlgebraQbarComplex : Algebra (AlgebraicClosure ℚ) ℂ :=
  complexEmbedding.toRingHom.toAlgebra
local instance instTowerQbarComplex : IsScalarTower ℚ (AlgebraicClosure ℚ) ℂ :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)


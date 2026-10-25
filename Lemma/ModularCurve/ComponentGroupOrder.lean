import Lemma.ModularCurve.ComponentGroup
import Theorems.Thm_ModularCurve_gramMap_injective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Def.ModularCurve_ComponentGroupOrder

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset Module

section GramMatrix
variable {ι : Type*} [Fintype ι] {κ : Type*}


@[simp] theorem gramMatrixOf_apply (e : ι → ℕ) (v : κ → characterLattice ι) (i j : κ) :
    gramMatrixOf e v i j = gramMap e (v i) (v j) :=
  rfl

end GramMatrix

section Engine
variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ] [DecidableEq κ] {e : ι → ℕ}


@[simp] theorem gramRangeBasisOf_coe (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) (i : κ) :
    (gramRangeBasisOf he c i : Module.Dual ℤ (characterLattice ι)) = gramMap e (c i) := by
  rw [gramRangeBasisOf, Basis.map_apply, LinearEquiv.ofInjective_apply]

theorem toMatrix_dualBasis_gramRangeOf (he : ∀ x, 0 < e x)
    (c : Basis κ ℤ (characterLattice ι)) :
    c.dualBasis.toMatrix ((↑) ∘ gramRangeBasisOf he c) =
      (gramMatrixOf e ⇑c).transpose := by
  ext i j
  rw [Basis.toMatrix_apply, Function.comp_apply, gramRangeBasisOf_coe, Basis.dualBasis_repr]
  rfl

end Engine

end ModularCurve

end

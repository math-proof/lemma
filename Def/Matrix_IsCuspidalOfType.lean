module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.FieldTheory.Finite.GaloisField
public import Def.Ideal_Mathlib430
public import Instance.CuspidalType_IsCuspidalOfType
public import Structure.CuspidalType_IsCuspidalOfType
public import Abbrev.CuspidalType_IsCuspidalOfType

@[expose] public section

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]


def diagElem (a : (ZMod q)ˣ) : GL2 q :=
  ⟨!![(a : ZMod q), 0; 0, 1], !![((a⁻¹ : (ZMod q)ˣ) : ZMod q), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]⟩

variable (k : Type*) [Field k]

noncomputable def coeffSum : (ProjLine q →₀ k) →ₗ[k] k :=
  Finsupp.linearCombination k fun _ => (1 : k)

noncomputable def steinberg : Subrepresentation (ind q k) where
  toSubmodule := LinearMap.ker (coeffSum q k)
  apply_mem_toSubmodule g v hv := by
    rw [LinearMap.mem_ker, coeffSum] at hv ⊢
    rw [show ind q k g v = Finsupp.mapDomain (g • ·) v from rfl, Finsupp.linearCombination_mapDomain]
    exact hv

noncomputable abbrev steinbergRep : Representation k (GL2 q) (steinberg q k).toSubmodule :=
  (steinberg q k).toRepresentation

noncomputable def constFun : ProjLine q →₀ k :=
  Finsupp.equivFunOnFinite.symm fun _ => (1 : k)

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]


end CuspidalType

end

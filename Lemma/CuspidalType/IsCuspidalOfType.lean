import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finite.GaloisField
import Lemma.Compat.Mathlib430
import Instance.CuspidalType_IsCuspidalOfType
import Structure.CuspidalType_IsCuspidalOfType
import Abbrev.CuspidalType_IsCuspidalOfType

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]


def diagElem (a : (ZMod q)ˣ) : GL2 q :=
  ⟨!![(a : ZMod q), 0; 0, 1], !![((a⁻¹ : (ZMod q)ˣ) : ZMod q), 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.inv_coe_unit]⟩

@[scoped simp] theorem diagElem_val (a : (ZMod q)ˣ) :
    (diagElem q a : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, 1] := rfl

@[scoped simp] theorem unipotent_val (t : ZMod q) :
    (unipotent q t : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, t; 0, 1] := rfl

theorem card_projLine : Nat.card (ProjLine q) = q + 1 := by
  rw [Projectivization.card_of_finrank_two (ZMod q) (Fin 2 → ZMod q) (by simp), Nat.card_zmod]

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

theorem coeffSum_constFun : coeffSum q k (constFun q k) = (q : k) + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  have hcard : (Fintype.card (ProjLine q) : k) = (q : k) + 1 := by
    rw [← Nat.card_eq_fintype_card, card_projLine]; push_cast; rfl
  rw [coeffSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun _ => zero_smul k (1 : k))]
  simp only [constFun, Finsupp.coe_equivFunOnFinite_symm, one_smul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact hcard

theorem constFun_mem_steinberg_iff : constFun q k ∈ (steinberg q k).toSubmodule ↔ (q : k) + 1 = 0 := by
  change constFun q k ∈ LinearMap.ker (coeffSum q k) ↔ _
  rw [LinearMap.mem_ker, coeffSum_constFun]

theorem finrank_ind : Module.finrank k (ProjLine q →₀ k) = q + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, card_projLine]


variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]


end CuspidalType

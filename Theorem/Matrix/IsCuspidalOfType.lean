module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.FieldTheory.Finite.GaloisField
public import Theorem.Ideal.Mathlib430
public import Instance.CuspidalType_IsCuspidalOfType
public import Structure.CuspidalType_IsCuspidalOfType
public import Abbrev.CuspidalType_IsCuspidalOfType

public section

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]


@[scoped simp] public theorem diagElem_val (a : (ZMod q)ˣ) :
    (diagElem q a : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![(a : ZMod q), 0; 0, 1] := rfl


@[scoped simp] public theorem unipotent_val (t : ZMod q) :
    (unipotent q t : Matrix (Fin 2) (Fin 2) (ZMod q)) = !![1, t; 0, 1] := rfl


public theorem card_projLine : Nat.card (ProjLine q) = q + 1 := by
  rw [Projectivization.card_of_finrank_two (ZMod q) (Fin 2 → ZMod q) (by simp), Nat.card_zmod]

variable (k : Type*) [Field k]


public theorem coeffSum_constFun : coeffSum q k (constFun q k) = (q : k) + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  have hcard : (Fintype.card (ProjLine q) : k) = (q : k) + 1 := by
    rw [← Nat.card_eq_fintype_card, card_projLine]; push_cast; rfl
  rw [coeffSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun _ => zero_smul k (1 : k))]
  simp only [constFun, Finsupp.coe_equivFunOnFinite_symm, one_smul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  exact hcard


public theorem constFun_mem_steinberg_iff : constFun q k ∈ (steinberg q k).toSubmodule ↔ (q : k) + 1 = 0 := by
  change constFun q k ∈ LinearMap.ker (coeffSum q k) ↔ _
  rw [LinearMap.mem_ker, coeffSum_constFun]


public theorem finrank_ind : Module.finrank k (ProjLine q →₀ k) = q + 1 := by
  classical
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, card_projLine]


variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]


end CuspidalType

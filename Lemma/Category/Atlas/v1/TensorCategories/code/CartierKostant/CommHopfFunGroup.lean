import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.CartierKostant.CommHopfFunGroup
open Coalgebra HopfAlgebra
open scoped TensorProduct


/--
[Lemma_1_33_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/CommHopfFunGroup.lean)
-/
@[path]
lemma Lemma_1_33_2
  {k : Type u}
  {V : Type u}
  [Field k]
  [CharZero k]
  [AddCommGroup V]
  [Module k V]
  {u : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V}
-- given
  (hsymm : SymmetricAlgebra.IsSymmetricTensor k V u)
  (hcocycle : SymmetricAlgebra.IsCocycle2 k V u) :
-- imply
  SymmetricAlgebra.IsCoboundary2 k V u :=
-- proof
  SymmetricAlgebra.symmetric_cocycle_is_coboundary k V u hsymm hcocycle

/--
[funAlgEquivInducedMap_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/CommHopfFunGroup.lean)
-/
@[path]
private lemma funAlgEquivInducedMap_spec_eq
  {k : Type u}
  [Field k]
  {G₁ : Type v}
  [Fintype G₁]
  [DecidableEq G₁]
  {e : (G₁ → k) ≃ₐ[k] (G₂ → k)}
  {g₂ : G₂}
  {f : G₁ → k} :
-- imply
  f (funAlgEquivInducedMap e g₂) = (e f) g₂ := by
-- proof
  apply funAlgEquivInducedMap_spec e g₂ f

/--
[funAlgEquivInducedMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/CommHopfFunGroup.lean)
-/
@[path]
private lemma funAlgEquivInducedMap_injective_eq
  {k : Type u}
  [Field k]
  {G₁ : Type v}
  [Fintype G₁]
  [DecidableEq G₁]
  {e : (G₁ → k) ≃ₐ[k] (G₂ → k)} :
-- imply
  Function.Injective (funAlgEquivInducedMap e) := by
-- proof
  apply funAlgEquivInducedMap_injective e


-- created on 2026-10-23

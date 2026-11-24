module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Theorem.v1.Atlas.TensorCategories.code.VecPivotal.SphericalInstance
open CategoryTheory MonoidalCategory Module Category TensorCategories


public section

namespace TensorCategories

/--
[vec_finrank_dual_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal/SphericalInstance.lean)
-/
@[path]
theorem vec_finrank_dual_eq
  {k : Type u}
  [Field k]
  {V : FGModuleCat.{u} k} :
-- imply
  Module.finrank k V = Module.finrank k (Vᘁ : FGModuleCat.{u} k) :=
-- proof
  (Subspace.dual_finrank_eq).symm
/-- The pivotal dimension of a finite-dimensional vector space `V` equals
`dim_k(V)` times the identity of the unit object in `FGModuleCat k`. -/
end TensorCategories



-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.CartierKostant.Axioms.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.CartierKostant.Axioms
open scoped TensorProduct


namespace Lemma1332

/--
[symmetric_cocycle_is_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_33_2.lean)
-/
@[path]
lemma symmetric_cocycle_is_coboundary
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

end Lemma1332


-- created on 2026-10-23

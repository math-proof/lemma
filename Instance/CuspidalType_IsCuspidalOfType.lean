-- Carved from Lemma/Definitions/Def_CuspidalType_IsCuspidalOfType.lean: instance decls only.
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finite.GaloisField
import Instance.Compat_Mathlib430
import Lemma.CuspidalType.IsCuspidalOfType

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]

scoped instance instMulActionProjLine : MulAction (GL2 q) (ProjLine q) :=
  MulAction.compHom (ProjLine q)
    (Matrix.GeneralLinearGroup.toLin (n := Fin 2) (R := ZMod q)).toMonoidHom

variable (k : Type*) [Field k]

variable {q} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

end CuspidalType

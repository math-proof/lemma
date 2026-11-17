-- Carved from Lemma/Definitions/Def_CuspidalType_IsCuspidalOfType.lean: instance decls only.

module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.FieldTheory.Finite.GaloisField
public import Instance.Compat_Mathlib430

@[expose] public section

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

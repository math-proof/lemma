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

abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)

abbrev ProjLine : Type := Projectivization (ZMod q) (Fin 2 → ZMod q)


noncomputable abbrev ind : Representation k (GL2 q) (ProjLine q →₀ k) :=
  Representation.ofMulActionFinsupp k (GL2 q) (ProjLine q)


end CuspidalType

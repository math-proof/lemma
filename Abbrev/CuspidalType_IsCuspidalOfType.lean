import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.Finite.GaloisField
import Instance.Compat_Mathlib430

set_option autoImplicit false

open Polynomial

namespace CuspidalType

variable (q : ℕ) [Fact q.Prime]

abbrev GL2 : Type := Matrix.GeneralLinearGroup (Fin 2) (ZMod q)

abbrev ProjLine : Type := Projectivization (ZMod q) (Fin 2 → ZMod q)


noncomputable abbrev ind : Representation k (GL2 q) (ProjLine q →₀ k) :=
  Representation.ofMulActionFinsupp k (GL2 q) (ProjLine q)


end CuspidalType

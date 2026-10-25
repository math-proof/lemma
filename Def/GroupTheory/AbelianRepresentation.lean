/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/AbelianRepresentation.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Analysis.Complex.Polynomial.Basic
open CategoryTheory
open scoped IsMulCommutative


namespace MathlibExt.GroupTheory.AbelianRepresentationWanted

/-- The character of a simple representation of a multiplicatively commutative monoid, bundled as
a monoid homomorphism. -/
noncomputable def _root_.FDRep.characterMonoidHom
    {k G : Type*} [Field k] [IsAlgClosed k] [Monoid G] [IsMulCommutative G]
    (V : FDRep k G) [Simple V] : G →* k where
  toFun := V.character
  map_one' := by simp [V.finrank_eq_one_of_isMulCommutative]
  map_mul' := V.character_mul_of_simple

/-- The one-dimensional finite-dimensional representation associated to a monoid homomorphism into
a field. -/
noncomputable def _root_.FDRep.ofMonoidHom {k G : Type*} [Field k] [Monoid G]
    (φ : G →* k) : FDRep k G :=
  FDRep.of
    { toFun := fun g => φ g • (LinearMap.id : k →ₗ[k] k)
      map_one' := by
        ext
        simp
      map_mul' := by
        intro g h
        ext
        simp [mul_smul, mul_comm] }

end MathlibExt.GroupTheory.AbelianRepresentationWanted

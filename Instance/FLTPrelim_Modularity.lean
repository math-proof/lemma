-- Carved from Lemma/Definitions/Def_FLTPrelim_Modularity.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Finite.Card
import Mathlib.Data.ZMod.Basic
import Def.FLTPrelim_Modularity

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

universe u


namespace WeierstrassCurve

namespace Affine

variable {R : Type u} [CommRing R] {W' : Affine R}

instance Point.instFinite [Finite R] : Finite W'.Point :=
  Finite.of_injective _ Point.toOptionPair_injective

end Affine


open CuspForm

end WeierstrassCurve

end

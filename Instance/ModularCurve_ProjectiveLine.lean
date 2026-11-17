-- Carved from Lemma/Definitions/Def_ModularCurve_ProjectiveLine.lean: instance decls only.
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Basic.Finite.Prod
import Lemma.SpecialLinearGroup.ProjectiveLine

namespace ModularCurve

open Matrix
open scoped MatrixGroups

section ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]

instance instUnimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R) :=
  unimodularRowSetoid R

instance instFiniteProjectiveLine [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

end ProjectiveLine


end ModularCurve

-- Carved from Lemma/Definitions/Def_ModularCurve_ProjectiveLine.lean: instance decls only.
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Basic.Finite.Prod
public import Theorem.SpecialLinearGroup.ProjectiveLine
public import Def.ModularCurve_ProjectiveLine
@[expose] public section

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

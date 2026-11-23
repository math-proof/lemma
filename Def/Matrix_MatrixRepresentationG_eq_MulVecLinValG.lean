module

public import Initialize.Tactic.Attr.Basic
public import Mathlib

@[expose] public section

open Matrix


namespace Deformation

def matrixRepresentation {n : Type} [Fintype n] [DecidableEq n] [Group G] [Field k] (rho : MonoidHom G (GL n k)) : Representation k G (n → k) := (Units.coeHom _).comp (GeneralLinearGroup.toLin.toMonoidHom.comp rho)

end Deformation

open Deformation

end

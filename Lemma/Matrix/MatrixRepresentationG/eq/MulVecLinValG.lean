import sympy.Basic
import Mathlib
open Matrix


namespace Deformation

def matrixRepresentation {n : Type} [Fintype n] [DecidableEq n] [Group G] [Field k] (rho : MonoidHom G (GL n k)) : Representation k G (n → k) := (Units.coeHom _).comp (GeneralLinearGroup.toLin.toMonoidHom.comp rho)

end Deformation

open Deformation


@[path]
private lemma main
  [Group G]
  [Field k]
  {n : Type} [Fintype n] [DecidableEq n]
-- given
  (rho : MonoidHom G (GL n k))
  (g : G) :
-- imply
  matrixRepresentation rho g = mulVecLin (rho g).val := by
-- proof
  apply GeneralLinearGroup.coe_toLin


-- created on 2026-10-24

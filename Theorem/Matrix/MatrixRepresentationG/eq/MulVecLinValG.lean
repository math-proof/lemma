module

public import Initialize.Tactic.Attr.Basic
public import Mathlib

public section

open Matrix


namespace Deformation


@[path]
private theorem main
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

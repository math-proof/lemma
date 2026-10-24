import Mathlib

set_option autoImplicit false

namespace ModularCurve

namespace JOneP

structure NeronSpecialFibreGeom (p : ℕ) : Type 1 where

  J0s : Type
  [instJ0s : AddCommGroup J0s]

  torus : AddSubgroup J0s

  JI : Type
  [instJI : AddCommGroup JI]
  JE : Type
  [instJE : AddCommGroup JE]

  proj : J0s →+ JI × JE
  proj_surjective : Function.Surjective proj
  ker_proj : proj.ker = torus

attribute [instance] NeronSpecialFibreGeom.instJ0s NeronSpecialFibreGeom.instJI NeronSpecialFibreGeom.instJE

end JOneP

end ModularCurve

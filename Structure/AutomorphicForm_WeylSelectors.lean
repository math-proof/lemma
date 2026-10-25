import Def.NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped Classical Pointwise

namespace AutomorphicForm.WeylIntegrable

section Generic

variable {A : Type*} [CommRing A] {ε y z x : A}

structure SelRel (ε y z x : A) : Prop where
  idem : ε * ε = ε
  yz : y * z = 1
  small : (1 - ε) * y = 1 - ε
  big : ε * y = ε * x


end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]


end Adelic

section Lattice

variable (F : Type) [Field F] [NumberField F]


end Lattice

section Modulus

variable (F : Type) [Field F] [NumberField F]


end Modulus

end AutomorphicForm.WeylIntegrable

end

import Mathlib

open MeasureTheory UpperHalfPlane Set
open scoped MatrixGroups ENNReal RealInnerProductSpace

noncomputable section

namespace FLT.L2Carrier

abbrev AutomorphicL2 (D : Set ℍ) : Type :=
  Lp ℂ 2 ((volume : Measure ℍ).restrict D)

end FLT.L2Carrier
end

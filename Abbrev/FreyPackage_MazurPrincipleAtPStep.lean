module
public import Mathlib
public import Def.FreyPackage_LoweringAtUniform
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine.Point


public section

namespace FreyPackage

abbrev MazurPrincipleAtPStep (P : FreyPackage) : Prop :=
  ∀ M : ℕ,
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    0 < M → ¬ P.p ∣ M → P.ModularRepOfLevelAt (M * P.p) →
    P.ModularRepOfLevelAt M

end FreyPackage

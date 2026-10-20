import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.PascalTheorem
open MetaMathlibExt


/--
[pascal_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PascalTheorem.lean)
-/
@[path]
private lemma pascal_theorem_eq
  [Field k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V]
  {O : P}
  {v : Fin 6 → P}
  {B3 : LinearMap.BilinForm k (V × k)}
  {q₁ q₂ q₃ : P}
-- given
  (hDim : Module.finrank k V = 2)
  (hChar : (2 : k) ≠ 0)
  (hB3_symm : B3.IsSymm)
  (hB3_nondeg : B3.Nondegenerate)
  (hConic : ∀ i, B3 ((v i -ᵥ O), 1) ((v i -ᵥ O), 1) = 0)
  (hInj : Function.Injective v)
  (hLine₁ : ¬ Collinear k {v 0, v 1, v 3, v 4})
  (hLine₂ : ¬ Collinear k {v 1, v 2, v 4, v 5})
  (hLine₃ : ¬ Collinear k {v 2, v 3, v 5, v 0})
  (hMeet₁ : Collinear k {v 0, v 1, q₁} ∧ Collinear k {v 3, v 4, q₁})
  (hMeet₂ : Collinear k {v 1, v 2, q₂} ∧ Collinear k {v 4, v 5, q₂})
  (hMeet₃ : Collinear k {v 2, v 3, q₃} ∧ Collinear k {v 5, v 0, q₃}) :
-- imply
  Collinear k {q₁, q₂, q₃} := by
-- proof
  apply MetaMathlibExt.pascal_theorem hDim hChar O v B3 hB3_symm hB3_nondeg q₁ q₂ q₃ hConic hInj hLine₁ hLine₂ hLine₃ hMeet₁ hMeet₂ hMeet₃


-- created on 2026-10-20

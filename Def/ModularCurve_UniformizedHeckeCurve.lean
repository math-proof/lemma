import Mathlib.SetTheory.Cardinal.Finite
import Def.ModularCurve_ComplexPlaceDictionary
import Def.ModularForm_HeckeOperator

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve


section Level

variable (N : ℕ)

def gamma0GL : Subgroup (GL (Fin 2) ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

def heckePoints (ℓ : ℕ) (_hℓ : ℓ.Prime) : Multiset (GL (Fin 2) ℝ) :=
  (Finset.range ℓ).val.map (fun j => ModularForm.heckeMatrix ℓ j) +
    (if ℓ ∣ N then 0 else {ModularForm.heckeDiagMatrix ℓ})

end Level

end ModularCurve

end

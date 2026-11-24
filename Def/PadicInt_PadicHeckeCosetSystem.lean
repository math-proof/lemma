module
public import Mathlib
public import Def.Matrix_HeckeCosetLocal
public import Structure.LocalLanglands_HeckeCosetSystem
public import Instance.LocalLanglands_PadicHeckeCosetSystem
set_option autoImplicit false
open scoped Pointwise ENNReal
open MulAction MeasureTheory


public section

namespace HeckeIntegralSeam

section Padic

open LocalGL2

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable abbrev padicDiagP : GL (Fin 2) ℚ_[p] :=
  diagPi (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p)

noncomputable def padicHeckeRep : Option (ZMod p) → GL (Fin 2) ℚ_[p]
  | some c => localRepSome (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p) ((ZMod.val c : ℕ) : ℤ_[p])
  | none => localRepInf (p : ℤ_[p]) (algebraMap_natCast_p_ne_zero p)

end Padic

end HeckeIntegralSeam

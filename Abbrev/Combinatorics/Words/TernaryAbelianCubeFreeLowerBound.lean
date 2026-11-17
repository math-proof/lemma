/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/TernaryAbelianCubeFreeLowerBound.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.Count
public import Mathlib.Data.Set.Card
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound

@[expose] public section


namespace MetaMathlibExt

section

abbrev ac_Tpl : Type :=
  (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))

end
end MetaMathlibExt

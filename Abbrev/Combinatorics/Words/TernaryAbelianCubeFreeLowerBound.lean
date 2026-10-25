/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/TernaryAbelianCubeFreeLowerBound.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Count
import Mathlib.Data.Set.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Ring
import Def.Combinatorics.Words.TernaryAbelianCubeFreeLowerBound


namespace MetaMathlibExt

section

abbrev ac_Tpl : Type :=
  (Fin 3 × Fin 3 × Fin 3 × Fin 3) × ((ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ))

end
end MetaMathlibExt

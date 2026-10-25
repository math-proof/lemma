import Mathlib
import Theorem.Analysis.Misc.erdos_613.Part5
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-! # Splitting the {name}`apex` red neighbors by parts -/

-- These came from the previous step you have:
-- def redNeighbors (color : Sym2 V → Fin 2) : Finset V := ...

/-- Further refine {name}`redBlock1` into its {name}`A1` and {name}`B1` parts. -/
noncomputable def redBlock1A1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA1 v)

noncomputable def redBlock1B1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB1 v)

/-- Further refine {name}`redBlock2` into its {name}`A2` and {name}`B2` parts. -/
noncomputable def redBlock2A2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isA2 v)

noncomputable def redBlock2B2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => isB2 v)

end PikhurkoN5

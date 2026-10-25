import Mathlib
import Theorem.Analysis.Misc.erdos_613.Part2
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-! # Red neighbors of the apex are ≥ 11 if there is no blue star `K_{1,5}` -/

/-- The set of blue neighbors of {name}`apex` in color class {lean (type := "Fin 2")}`0`. -/
noncomputable def blueNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (s(apex, v)) = 0)

/-- The set of red neighbors of {name}`apex` in color class {lean (type := "Fin 2")}`1`. -/
noncomputable def redNeighbors (color : Sym2 V → Fin 2) : Finset V :=
  (G.neighborFinset apex).filter (fun v => color (s(apex, v)) = 1)

end PikhurkoN5

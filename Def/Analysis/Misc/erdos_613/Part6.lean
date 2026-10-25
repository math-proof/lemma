import Mathlib
import Instance.Analysis.Misc.erdos_613
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- Red neighbors of {name}`apex` that lie in the first block {name}`A1`/{name}`B1`. -/
noncomputable def redBlock1 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => inBlock1 v)

/-- Red neighbors of {name}`apex` that lie in the second block {name}`A2`/{name}`B2`.

We implement this as the *complement* of {name}`inBlock1` inside {name}`redNeighbors`.
Since {name}`apex` is not in {name}`redNeighbors`, this is exactly the {name}`A2`/{name}`B2` part. -/
noncomputable def redBlock2 (color : Sym2 V → Fin 2) : Finset V :=
  (redNeighbors color).filter (fun v => ¬ inBlock1 v)

end PikhurkoN5

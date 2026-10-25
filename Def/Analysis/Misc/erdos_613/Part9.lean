import Mathlib
import Theorem.Analysis.Misc.erdos_613.Part6
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-! # Bounding the {lit}`B`-parts by {lean}`5` -/

/-- All {name}`B1`-vertices as a finset (image of {lean}`Fin 5`). -/
def B1Set : Finset V := (Finset.univ.image fun j : Fin 5 => B1 j)

/-- All {name}`B2`-vertices as a finset (image of {lean}`Fin 5`). -/
def B2Set : Finset V := (Finset.univ.image fun j : Fin 5 => B2 j)

end PikhurkoN5

import Mathlib
import Theorem.Analysis.Misc.erdos_613.Part3
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- Membership in the first block {name}`A1`/{name}`B1`. -/
def inBlock1 : V → Prop
| A1 _ => True
| B1 _ => True
| _    => False

end PikhurkoN5

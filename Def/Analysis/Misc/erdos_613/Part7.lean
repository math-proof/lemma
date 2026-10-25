import Mathlib
import Theorem.Analysis.Misc.erdos_613.Part4
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-! # Part / block predicates -/

/-- Recognizes the clique side {name}`A1`. -/
def isA1 : V → Prop
| A1 _ => True | _ => False

/-- Recognizes the independent side {name}`B1`. -/
def isB1 : V → Prop
| B1 _ => True | _ => False

/-- Recognizes the clique side {name}`A2`. -/
def isA2 : V → Prop
| A2 _ => True | _ => False

/-- Recognizes the independent side {name}`B2`. -/
def isB2 : V → Prop
| B2 _ => True | _ => False

/-- Second block {name}`A2`/{name}`B2`. -/
def inBlock2 : V → Prop
| A2 _ => True | B2 _ => True | _ => False

end PikhurkoN5

module

public import Mathlib
public import Def.Analysis.Misc.erdos_613.Part5
@[expose] public section

open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

noncomputable instance : DecidablePred inBlock1 := by
  intro v; cases v <;> infer_instance

end PikhurkoN5

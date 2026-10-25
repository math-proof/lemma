import Mathlib
import Def.Analysis.Misc.erdos_613.Part7
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

noncomputable instance : DecidablePred isA1 := by intro v; cases v <;> infer_instance

noncomputable instance : DecidablePred isB1 := by intro v; cases v <;> infer_instance

noncomputable instance : DecidablePred isA2 := by intro v; cases v <;> infer_instance

noncomputable instance : DecidablePred isB2 := by intro v; cases v <;> infer_instance

noncomputable instance : DecidablePred inBlock1 := by intro v; cases v <;> infer_instance

noncomputable instance : DecidablePred inBlock2 := by intro v; cases v <;> infer_instance

end PikhurkoN5

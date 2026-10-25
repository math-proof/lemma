/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

/-- Width-independent facts preserved by every adaptive-minrun call. -/
structure MinrunRangeInv (state : MinrunState) : Prop where
  listMax : state.listlen.toNat ≤ PY_LIST_MAX
  exponent60 : state.mr_e.toNat ≤ 60
  current : state.mr_current.toNat < 2 ^ state.mr_e.toNat
  mask : state.mr_mask.toNat < 2 ^ state.mr_e.toNat
  modulusLe : 2 ^ state.mr_e.toNat ≤ state.listlen.toNat
  floorLt : state.listlen.toNat / 2 ^ state.mr_e.toNat < 64

end CPythonListsort

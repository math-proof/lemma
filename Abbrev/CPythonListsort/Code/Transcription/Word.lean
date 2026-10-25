/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Word.lean -/

import Mathlib.Data.BitVec
/-!
# CPython finite-width words

The listsort transcription represents every non-pointer `Py_ssize_t` field by
an explicit 64-bit word. Signed operations use `BitVec.slt` and
`BitVec.sle`, together with `BitVec.sshiftRight`; unsigned projections appear
only where C performs an unsigned cast or in specifications and proofs.
-/


namespace CPythonListsort

/-- The fixed-width representation of CPython's `Py_ssize_t` in this project. -/
abbrev PySSize := BitVec 64

end CPythonListsort

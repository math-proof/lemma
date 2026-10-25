import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.RingTheory.ConductorIdeal.Part2


/--
[mem_diagSubalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma mem_diagSubalgebra
  {p : ℤ × ℤ} :
-- imply
  p ∈ diagSubalgebra ↔ p.1 = p.2 :=
-- proof
  Iff.rfl


-- created on 2026-10-23

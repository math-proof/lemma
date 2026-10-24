/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean -/


import sympy.atlas.NumberTheory.AppellSequence

open MetaMathlibExt

private noncomputable def monomialSeq : ℕ → Polynomial ℚ :=
  fun n => Polynomial.X ^ n

private noncomputable def zeroSeq : ℕ → Polynomial ℚ :=
  fun _ => 0

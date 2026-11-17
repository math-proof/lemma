/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/AppellSequence.lean -/


module

public import Def.NumberTheory.AppellSequence

@[expose] public section

open MetaMathlibExt


noncomputable def monomialSeq : ℕ → Polynomial ℚ :=
  fun n => Polynomial.X ^ n

noncomputable def zeroSeq : ℕ → Polynomial ℚ :=
  fun _ => 0


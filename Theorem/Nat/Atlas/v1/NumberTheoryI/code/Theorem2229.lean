module

public import Mathlib
public import Structure.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT

public section

open NumberField RayClassField


namespace NormIndexInequality

/--
[norm_index_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Theorem2229.lean)
-/
public theorem norm_index_inequality
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [IsGalois K L]
  {𝔪 : Modulus K}
-- given
  (h_cond : Modulus.dvd (GlobalCFT.extensionConductor K L) 𝔪) :
-- imply
  (GlobalCFT.NormGroup K L 𝔪).index ≤ Module.finrank K L :=
-- proof
  GlobalCFT.theorem_22_29_norm_index_inequality K L 𝔪 h_cond

end NormIndexInequality


-- created on 2026-10-23

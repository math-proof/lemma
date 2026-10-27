import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFTMain.Part2
open NumberField RayClassField GlobalCFT


namespace GlobalCFT

/--
[CongruenceSubgroup.ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFTMain.lean)
-/
@[path]
lemma CongruenceSubgroup.ext
  {K : Type u}
  [Field K]
  [NumberField K]
  {K}
  {𝔪 : Modulus K}
  {𝒞₁ 𝒞₂ : CongruenceSubgroup K 𝔪}
-- given
  (h : 𝒞₁.toSubgroup = 𝒞₂.toSubgroup) :
-- imply
  𝒞₁ = 𝒞₂ := by
-- proof
  cases 𝒞₁; cases 𝒞₂; simp only [mk.injEq]; exact h

end GlobalCFT


-- created on 2026-10-23

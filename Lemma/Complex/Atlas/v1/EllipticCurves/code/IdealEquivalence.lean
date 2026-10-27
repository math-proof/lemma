import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.EllipticCurves.code.IdealEquivalence.Part2
open IdealEquivalence
open ComplexLattice Pointwise


namespace IdealEquivalence

/--
[IsEquivalent.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean)
-/
@[path]
lemma IsEquivalent.symm
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ComplexLattice.ProperIdeal 𝒪}
-- given
  (h : IsEquivalent 𝒪 L₁ L₂) :
-- imply
  IsEquivalent 𝒪 L₂ L₁ :=
-- proof
  ComplexLattice.IsEquivalent.symm h

end IdealEquivalence

namespace IdealEquivalence

/--
[IdealClassGroup.mk_eq_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean)
-/
@[path]
lemma IdealClassGroup.mk_eq_mk_iff
  {𝒪 : Subring ℂ}
  {L₁ L₂ : ComplexLattice.ProperIdeal 𝒪} :
-- imply
  IdealClassGroup.mk 𝒪 L₁ = IdealClassGroup.mk 𝒪 L₂ ↔ IsEquivalent 𝒪 L₁ L₂ :=
-- proof
  Quotient.eq (r := properIdealSetoid 𝒪)

end IdealEquivalence

/--
[IsEquivalent.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean)
-/
@[path]
private lemma refl_eq
  {𝒪 : Subring ℂ}
  {L : ComplexLattice.ProperIdeal 𝒪} :
-- imply
  IsEquivalent 𝒪 L L := by
-- proof
  apply IdealEquivalence.IsEquivalent.refl 𝒪 L

/--
[IsEquivalent.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean)
-/
@[path]
private lemma trans_eq
  {𝒪 : Subring ℂ}
  {L₁ L₂ L₃ : ComplexLattice.ProperIdeal 𝒪}
-- given
  (h₁₂ : IsEquivalent 𝒪 L₁ L₂)
  (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
-- imply
  IsEquivalent 𝒪 L₁ L₃ := by
-- proof
  apply IdealEquivalence.IsEquivalent.trans h₁₂ h₂₃

/--
[isEquivalent_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IdealEquivalence.lean)
-/
@[path]
private lemma isEquivalent_equivalence_eq
  {𝒪 : Subring ℂ} :
-- imply
  Equivalence (IsEquivalent 𝒪) := by
-- proof
  apply IdealEquivalence.isEquivalent_equivalence 𝒪


-- created on 2026-10-23

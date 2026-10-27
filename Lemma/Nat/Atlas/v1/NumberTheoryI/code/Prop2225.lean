import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Prop2225
open NumberField RayClassField GlobalConductor KroneckerWeber ConductorRamification


namespace ConductorRamification

/--
[conductorVal_eq_zero_iff_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2225.lean)
-/
@[path]
lemma conductorVal_eq_zero_iff_unramified
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔭 : Prime' K} :
-- imply
  (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 0 ↔ GlobalCFT.IsUnramifiedIn K L 𝔭 :=
-- proof
  GlobalCFT.proposition_22_25_unramified K L 𝔭

end ConductorRamification

namespace ConductorRamification

/--
[conductorVal_eq_one_iff_tamelyRamified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2225.lean)
-/
@[path]
lemma conductorVal_eq_one_iff_tamelyRamified
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔭 : Prime' K} :
-- imply
  (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 1 ↔ (GlobalCFT.IsTamelyRamifiedIn K L 𝔭 ∧ ¬ GlobalCFT.IsUnramifiedIn K L 𝔭) :=
-- proof
  GlobalCFT.proposition_22_25_tame K L 𝔭

end ConductorRamification

namespace ConductorRamification

/--
[conductorVal_ge_two_iff_wildlyRamified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2225.lean)
-/
@[path]
lemma conductorVal_ge_two_iff_wildlyRamified
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔭 : Prime' K} :
-- imply
  2 ≤ (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) ↔ GlobalCFT.IsWildlyRamifiedIn K L 𝔭 :=
-- proof
  GlobalCFT.proposition_22_25_wild K L 𝔭

end ConductorRamification

namespace ConductorRamification

/--
[proposition_22_25](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2225.lean)
-/
@[path]
lemma proposition_22_25
  {K : Type u}
  [Field K]
  [NumberField K]
  {𝔭 : Prime' K} :
-- imply
  ((GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 0 ↔ GlobalCFT.IsUnramifiedIn K L 𝔭) ∧ ((GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 1 ↔ (GlobalCFT.IsTamelyRamifiedIn K L 𝔭 ∧ ¬ GlobalCFT.IsUnramifiedIn K L 𝔭)) ∧ (2 ≤ (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) ↔ GlobalCFT.IsWildlyRamifiedIn K L 𝔭) :=
-- proof
  ⟨conductorVal_eq_zero_iff_unramified 𝔭,
    conductorVal_eq_one_iff_tamelyRamified 𝔭,
    conductorVal_ge_two_iff_wildlyRamified 𝔭⟩

end ConductorRamification


-- created on 2026-10-23

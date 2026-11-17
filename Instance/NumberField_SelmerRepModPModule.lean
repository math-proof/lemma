-- Carved out of Instance/NumberField_SelmerRepModP.lean so the MulDistribMulAction
-- instance and this ZMod module instance are not in the same file.
-- Registers `instModuleZModSelmer` from `selmerRepIntZModModule` in
-- `Lemma.Rep.SelmerRepModP`. The lemma must not import this module (cycle).
import Mathlib
import Lemma.Rep.SelmerRepModP

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace NumberField.LevelArith

section Selmer

variable (E F : Type) [Field E] [Field F] [NumberField E] [NumberField F] [Algebra E F]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ)

scoped instance instModuleZModSelmer : Module (ZMod p) (selmerRepInt E F S p) :=
  selmerRepIntZModModule E F S p

end Selmer


end NumberField.LevelArith

end

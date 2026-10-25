-- Carved from Lemma/Definitions/Def_LanglandsTunnell_ArtinCoreCTM.lean: instance decls only.
import Instance.LanglandsTunnell_ArtinFrobenius
import Def.M4aHerbrand_IdeleClassVocab
import Def.LanglandsTunnell_ArtinCoreCTM

set_option autoImplicit false

noncomputable section

open Deep.NTSupply NumberField IsDedekindDomain WithZero
open scoped nonZeroDivisors IsMulCommutative Pointwise


namespace LanglandsTunnell.P2.Artin

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter WithZero


section PerICore

set_option maxSynthPendingDepth 3

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance : CommGroup c.Ip := inferInstanceAs (CommGroup ↥(coprimeToModulus c.E (modulusExt K c.E c.𝔪)))

end PerICore


end LanglandsTunnell.P2.Artin
end

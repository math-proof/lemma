import Lemma.LanglandsTunnell.CubicInduction_Growth
import Def.LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction


section Roots

variable (F : Type) [Field F] [NumberField F]


theorem isGaugeMajorised3_zero : IsGaugeMajorised3 F (fun _ => (0 : ℂ)) :=
  ⟨0, ∅, 1, fun N => ⟨0, fun g => ⟨fun _ => rfl, fun _ => by simp⟩⟩⟩

end Roots

end LanglandsTunnell.CubicInduction

end

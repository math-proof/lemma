import Mathlib
import Def.LanglandsTunnell_RealizationDictionary
import Def.LanglandsTunnell_TunnellExistenceCarriers
import Def.LanglandsTunnell_WeightOneRealizationCarriers

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open FLT.ExplicitLift EisensteinWeightOne CuspForm Zsqrtd
open CongruenceSubgroup

noncomputable section


namespace AutomorphicForm

theorem realizationDictionary_of_weightOne_of_congruenceLift
    {notion : CuspidalityNotion (ℤ√(-2))}
    (hW1 : WeightOneHolomorphicRealization notion)
    (hW2 : CuspForm.WeightTwoModThreeCongruenceLift) :
    RealizationDictionary notion := by
  intro π₀ hcusp T
  obtain ⟨M, hM, b, c1, c2, c3, cW1, c6⟩ := hW1 π₀ hcusp T
  obtain ⟨c4, c5⟩ := hW2 M hM b c2 c3 cW1
  exact ⟨M, hM, b, c1, c2, c3, c4, c5, c6⟩

end AutomorphicForm

namespace LanglandsTunnell

theorem notionCompatForAttachedOctahedralData_self
    (notion : AutomorphicForm.CuspidalityNotion (ℤ√(-2))) :
    NotionCompatForAttachedOctahedralData notion notion :=
  fun _ _ _ _ _ _ _ _ h _ => h

end LanglandsTunnell

end

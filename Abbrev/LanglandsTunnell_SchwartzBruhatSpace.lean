import Def.LanglandsTunnell_TateLocalZeta
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatSpace

section Space

variable (X : Type*) [TopologicalSpace X]

abbrev testSpace : Submodule ℂ (X → ℂ) where
  carrier := {f | IsSchwartzBruhat f}
  zero_mem' := IsSchwartzBruhat.zero
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := by
    intro c f hf
    refine ⟨?_, ?_⟩
    · exact hf.1.comp (c * ·)
    · exact hf.2.comp_left (g := (c * ·)) (mul_zero c)

variable {X}


end Space

end SchwartzBruhatSpace

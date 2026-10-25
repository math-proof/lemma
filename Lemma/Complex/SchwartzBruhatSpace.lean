import Lemma.LanglandsTunnell.TateLocalZeta
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Abbrev.LanglandsTunnell_SchwartzBruhatSpace

set_option autoImplicit false

open LanglandsTunnell.TateLocal

noncomputable section

namespace SchwartzBruhatSpace

section Space

variable (X : Type*) [TopologicalSpace X]


theorem mem_testSpace {f : X → ℂ} : f ∈ testSpace X ↔ IsSchwartzBruhat f :=
  Iff.rfl

theorem mem_testSpace_iff {f : X → ℂ} : f ∈ testSpace X ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

theorem isLocallyConstant_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsLocallyConstant f :=
  hf.1

theorem hasCompactSupport_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : HasCompactSupport f :=
  hf.2

theorem mem_testSpace_of {f : X → ℂ} (h₁ : IsLocallyConstant f) (h₂ : HasCompactSupport f) :
    f ∈ testSpace X :=
  ⟨h₁, h₂⟩

theorem indicator_mem_testSpace {U : Set X} (hU : IsClopen U) (hUc : IsCompact U) (c : ℂ) :
    (U.indicator fun _ => c) ∈ testSpace X :=
  IsSchwartzBruhat.indicator_const hU hUc c

theorem mul_mem_testSpace {e f : X → ℂ} (he : IsLocallyConstant e) (hf : f ∈ testSpace X) :
    e * f ∈ testSpace X :=
  ⟨he.mul hf.1, hf.2.mul_left⟩

theorem isClopen_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsClopen (Function.support f) := by
  have h : Function.support f = {x | f x = 0}ᶜ := by
    ext x
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_setOf_eq, ne_eq]
  rw [h]
  exact (hf.1.isClopen_fiber 0).compl

theorem isCompact_support_of_mem {f : X → ℂ} (hf : f ∈ testSpace X) : IsCompact (Function.support f) :=
  (hasCompactSupport_of_mem hf).isCompact.of_isClosed_subset (isClopen_support_of_mem hf).isClosed (subset_tsupport _)

end Space

end SchwartzBruhatSpace

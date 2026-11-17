module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Def.Stickelberger_Basic

set_option autoImplicit false

public section

namespace Stickelberger


@[simp] lemma mem_exponentSet {p c : ℕ} :
    c ∈ exponentSet p ↔ 0 < c ∧ 2 * c < p := by
  simp only [exponentSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

end Stickelberger

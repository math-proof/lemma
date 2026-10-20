import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.ScalarCenter
open BurnsidePaqb


/--
[all_roots_eq_of_norm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma all_roots_eq_of_norm_eq_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (h : ‖ρ.character g‖ = Module.finrank ℂ V) :
-- imply
  ∀ μ₁ ∈ (ρ g).charpoly.roots, ∀ μ₂ ∈ (ρ g).charpoly.roots, μ₁ = μ₂ := by
-- proof
  apply BurnsidePaqb.all_roots_eq_of_norm_eq ρ g h

/--
[eq_smul_one_of_all_roots_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma eq_smul_one_of_all_roots_eq_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
  {μ₀ : ℂ}
-- given
  (hall : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀) :
-- imply
  (ρ g : Module.End ℂ V) = μ₀ • 1 := by
-- proof
  apply BurnsidePaqb.eq_smul_one_of_all_roots_eq ρ g μ₀ hall

/--
[mem_charCenter_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma mem_charCenter_iff_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G} :
-- imply
  g ∈ charCenter ρ ↔ ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 := by
-- proof
  apply BurnsidePaqb.mem_charCenter_iff ρ g

/--
[mem_charCenter_of_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma mem_charCenter_of_eq_smul_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G}
  {c : ℂ}
-- given
  (hc : (ρ g : Module.End ℂ V) = c • 1) :
-- imply
  g ∈ charCenter ρ := by
-- proof
  apply BurnsidePaqb.mem_charCenter_of_eq_smul ρ g c hc

/--
[exists_eq_smul_of_mem_charCenter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma exists_eq_smul_of_mem_charCenter_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (h : g ∈ charCenter ρ) :
-- imply
  ∃ c : ℂ, (ρ g : Module.End ℂ V) = c • 1 := by
-- proof
  apply BurnsidePaqb.exists_eq_smul_of_mem_charCenter ρ g h

/--
[charCenter_proper_of_nonlinear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma charCenter_proper_of_nonlinear_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
-- given
  (h : 1 < Module.finrank ℂ V) :
-- imply
  charCenter ρ ≠ ⊤ := by
-- proof
  apply BurnsidePaqb.charCenter_proper_of_nonlinear ρ h

/--
[norm_eq_of_mem_charCenter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/ScalarCenter.lean)
-/
@[path]
private lemma norm_eq_of_mem_charCenter_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] [Finite G]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (h : g ∈ charCenter ρ) :
-- imply
  ‖ρ.character g‖ = Module.finrank ℂ V := by
-- proof
  apply BurnsidePaqb.norm_eq_of_mem_charCenter ρ g h


-- created on 2026-10-20

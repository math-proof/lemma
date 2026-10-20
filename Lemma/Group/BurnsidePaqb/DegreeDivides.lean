import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.DegreeDivides
open BurnsidePaqb


/--
[self_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma self_pair_sum_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
-- proof
  apply BurnsidePaqb.self_pair_sum ρ

/--
[sum_over_classes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma sum_over_classes_eq
  [Group G] [Fintype G]
  {f : G → ℂ} :
-- imply
  ∑ g : G, f g
    = ∑ l : ConjClasses G, ∑ x ∈ (ConjClasses.carrier l).toFinset, f x := by
-- proof
  apply BurnsidePaqb.sum_over_classes f

/--
[conj_to_rep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma conj_to_rep_eq
  [Group G] [Fintype G]
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ∃ c : G, c * x * c⁻¹ = classRep l := by
-- proof
  apply BurnsidePaqb.conj_to_rep l x hx

/--
[char_eq_of_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma char_eq_of_mem_carrier_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ρ.character x = ρ.character (classRep l) := by
-- proof
  apply BurnsidePaqb.char_eq_of_mem_carrier ρ l x hx

/--
[char_inv_eq_of_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma char_inv_eq_of_mem_carrier_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ρ.character x⁻¹ = ρ.character (classRep l)⁻¹ := by
-- proof
  apply BurnsidePaqb.char_inv_eq_of_mem_carrier ρ l x hx

/--
[class_inner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma class_inner_sum_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x * ρ.character x⁻¹
    = (Module.finrank ℂ V : ℂ)
    * (centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
-- proof
  apply BurnsidePaqb.class_inner_sum ρ l

/--
[degree_dvd_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
private lemma degree_dvd_card_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  Module.finrank ℂ V ∣ Fintype.card G := by
-- proof
  apply BurnsidePaqb.degree_dvd_card ρ


-- created on 2026-10-20

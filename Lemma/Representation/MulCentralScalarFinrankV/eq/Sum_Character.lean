import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.CentralCharacter
open BurnsidePaqb


namespace BurnsidePaqb

/--
[centralScalar_trace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
lemma centralScalar_trace
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  centralScalar ρ l * Module.finrank ℂ V
    = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x := by
-- proof
  classical
  have hT : ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)
    = centralScalar ρ l • 1 := by
    ext v
    simp [centralScalar_spec]
  have htrace : LinearMap.trace ℂ V
    (ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset))
    = centralScalar ρ l * Module.finrank ℂ V := by
    have hid : (1 : Module.End ℂ V) = LinearMap.id := rfl
    rw [hT, map_smul, hid, LinearMap.trace_id, smul_eq_mul]
  have hexpand : ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset)
    = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ x := by
    change ρ.asAlgebraHom (∑ x ∈ (ConjClasses.carrier l).toFinset,
      MonoidAlgebra.of ℂ G x) = _
    rw [map_sum]
    simp only [Representation.asAlgebraHom_of]
  have hsum : LinearMap.trace ℂ V
    (ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset))
    = ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x := by
    rw [hexpand, map_sum]
    rfl
  rw [← htrace, hsum]

end BurnsidePaqb

namespace BurnsidePaqb

/--
[scalarSubalg_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
lemma scalarSubalg_fg
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  (scalarSubalg ρ).toSubmodule.FG := by
-- proof
  classical
  have : (scalarSubalg ρ).toSubmodule
    = Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := rfl
  rw [this]
  exact ⟨scalarGens ρ, rfl⟩

end BurnsidePaqb

namespace BurnsidePaqb

/--
[centralScalar_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
lemma centralScalar_isIntegral
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  IsIntegral ℤ (centralScalar ρ l) :=
-- proof
  IsIntegral.of_mem_of_fg (scalarSubalg ρ) (scalarSubalg_fg ρ) _
    (scalar_mem_scalarSpan ρ l)

end BurnsidePaqb

namespace BurnsidePaqb

/--
[classSum_centralScalar_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
lemma classSum_centralScalar_isIntegral
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G} :
-- imply
  IsIntegral ℤ ((conjClass g).card * ρ.character g / ρ.character 1) := by
-- proof
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hχ1ne : ρ.character 1 ≠ 0 := by
    rw [Representation.char_one]
    exact_mod_cast ne_of_gt hpos
  have hdiv : centralScalar ρ (ConjClasses.mk g)
    = (conjClass g).card * ρ.character g / ρ.character 1 := by
    rw [eq_div_iff hχ1ne]
    have hcarry : (ConjClasses.carrier (ConjClasses.mk g)).toFinset
      = conjClass g := by
      rw [carrier_toFinset]
      apply conjClass_eq_of_isConj
      rw [← ConjClasses.mk_eq_mk_iff_isConj]
      exact classRep_spec _
    have hchar : ∀ x ∈ conjClass g, ρ.character x = ρ.character g := by
      intro x hx
      rw [mem_conjClass_iff] at hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      have hcc := Representation.char_conj ρ x c
      rwa [hc] at hcc
    have hsum : ∑ x ∈ conjClass g, ρ.character x
      = (conjClass g).card * ρ.character g := by
      calc ∑ x ∈ conjClass g, ρ.character x
        = ∑ x ∈ conjClass g, ρ.character g :=
          Finset.sum_congr rfl (fun x hx => hchar x hx)
        _ = (conjClass g).card * ρ.character g := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have htrace := centralScalar_trace ρ (ConjClasses.mk g)
    rw [hcarry, hsum] at htrace
    rwa [Representation.char_one]
  rw [← hdiv]
  exact centralScalar_isIntegral ρ _

end BurnsidePaqb

/--
[exists_scalar_of_central](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma exists_scalar_of_central_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {z : MonoidAlgebra ℂ G}
-- given
  (hz : ∀ w, w * z = z * w) :
-- imply
  ∃ c : ℂ, ∀ v : V, ρ.asAlgebraHom z v = c • v := by
-- proof
  apply BurnsidePaqb.exists_scalar_of_central ρ z hz

/--
[centralScalar_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_spec_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G}
  {v : V} :
-- imply
  ρ.asAlgebraHom (classSum (ConjClasses.carrier l).toFinset) v
    = centralScalar ρ l • v := by
-- proof
  apply BurnsidePaqb.centralScalar_spec ρ l v

/--
[centralScalar_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma centralScalar_mul_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l1 l2 : ConjClasses G} :
-- imply
  centralScalar ρ l1 * centralScalar ρ l2
    = ∑ l, (structConst (conjClass (classRep l1)) (conjClass (classRep l2))
    (classRep l) : ℂ) * centralScalar ρ l := by
-- proof
  apply BurnsidePaqb.centralScalar_mul ρ l1 l2

/--
[one_mem_scalarSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma one_mem_scalarSpan_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  (1 : ℂ) ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.one_mem_scalarSpan ρ

/--
[scalar_mem_scalarSpan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma scalar_mem_scalarSpan_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  centralScalar ρ l ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.scalar_mem_scalarSpan ρ l

/--
[scalarGens_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/CentralCharacter.lean)
-/
@[path]
private lemma scalarGens_mul_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {a b : ℂ}
-- given
  (ha : a ∈ scalarGens ρ)
  (hb : b ∈ scalarGens ρ) :
-- imply
  a * b ∈ Submodule.span ℤ (↑(scalarGens ρ) : Set ℂ) := by
-- proof
  apply BurnsidePaqb.scalarGens_mul ρ a b ha hb


-- created on 2026-10-20
-- updated on 2026-10-23

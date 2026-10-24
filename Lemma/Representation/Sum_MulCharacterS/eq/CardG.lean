import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.BurnsidePaqb.KillingLemma
import Lemma.Representation.Character.eq.SumRootsCharpoly


namespace BurnsidePaqb

/--
[self_pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma self_pair_sum
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
-- proof
  classical
  have : Nonempty G := ⟨1⟩
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hc
  have hne : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
  have h := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left hne] at h
  have key : (Nat.card G : ℂ)⁻¹ * (∑ g : G, ρ.character g * ρ.character g⁻¹) = 1 := by
    simpa using h
  calc ∑ g : G, ρ.character g * ρ.character g⁻¹
    = (Nat.card G : ℂ)
      * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    _ = (Nat.card G : ℂ) := by rw [key, mul_one]

end BurnsidePaqb

namespace BurnsidePaqb

/--
[sum_over_classes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma sum_over_classes
  [Group G] [Fintype G]
  {f : G → ℂ} :
-- imply
  ∑ g : G, f g
    = ∑ l : ConjClasses G, ∑ x ∈ (ConjClasses.carrier l).toFinset, f x := by
-- proof
  let fiberEquiv (l : ConjClasses G) :
    ↥((ConjClasses.carrier l).toFinset) ≃ {x : G // ConjClasses.mk x = l} :=
    Set.equivOfEq (by
      ext x
      simp [ConjClasses.carrier_eq_preimage_mk]
      rfl)
  let e : (Σ l : ConjClasses G,
    ↥((ConjClasses.carrier l).toFinset)) ≃ G :=
    (Equiv.sigmaCongrRight fiberEquiv).trans
      (Equiv.sigmaFiberEquiv ConjClasses.mk)
  have h1 : ∑ p : (Σ l : ConjClasses G,
    ↥((ConjClasses.carrier l).toFinset)), f p.2.1 = ∑ g : G, f g := by
    exact Fintype.sum_equiv e (fun p => f p.2.1) f (fun p => by rfl)
  rw [← h1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  exact Finset.sum_coe_sort _ _

end BurnsidePaqb

namespace BurnsidePaqb

/--
[conj_to_rep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma conj_to_rep
  [Group G] [Fintype G]
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ∃ c : G, c * x * c⁻¹ = classRep l := by
-- proof
  have hmem : x ∈ ConjClasses.carrier l := Set.mem_toFinset.mp hx
  have hmk : ConjClasses.mk x = l := ConjClasses.mem_carrier_iff_mk_eq.mp hmem
  have hrep : ConjClasses.mk (classRep l) = l := classRep_spec l
  have hconj : IsConj x (classRep l) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (by rw [hmk, hrep])
  exact isConj_iff.mp hconj

end BurnsidePaqb

namespace BurnsidePaqb

/--
[char_eq_of_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma char_eq_of_mem_carrier
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ρ.character x = ρ.character (classRep l) := by
-- proof
  obtain ⟨c, hc⟩ := conj_to_rep l x hx
  have hcc := Representation.char_conj ρ x c
  rwa [hc] at hcc

end BurnsidePaqb

namespace BurnsidePaqb

/--
[char_inv_eq_of_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma char_inv_eq_of_mem_carrier
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {l : ConjClasses G}
  {x : G}
-- given
  (hx : x ∈ (ConjClasses.carrier l).toFinset) :
-- imply
  ρ.character x⁻¹ = ρ.character (classRep l)⁻¹ := by
-- proof
  obtain ⟨c, hc⟩ := conj_to_rep l x hx
  have hinv : c * x⁻¹ * c⁻¹ = (classRep l)⁻¹ := by rw [← hc]; group
  have hcc := Representation.char_conj ρ x⁻¹ c
  rwa [hinv] at hcc

end BurnsidePaqb

namespace BurnsidePaqb

/--
[class_inner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma class_inner_sum
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {l : ConjClasses G} :
-- imply
  ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x * ρ.character x⁻¹
    = (Module.finrank ℂ V : ℂ)
    * (centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
-- proof
  have h1 : ∀ x ∈ (ConjClasses.carrier l).toFinset,
    ρ.character x * ρ.character x⁻¹
      = ρ.character (classRep l) * ρ.character (classRep l)⁻¹ := by
    intro x hx
    rw [char_eq_of_mem_carrier ρ l x hx, char_inv_eq_of_mem_carrier ρ l x hx]
  have hsum : ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x
    = ((ConjClasses.carrier l).toFinset.card : ℂ) * ρ.character (classRep l) := by
    rw [Finset.sum_congr rfl (fun x hx => char_eq_of_mem_carrier ρ l x hx),
      Finset.sum_const, nsmul_eq_mul]
  have htrace := centralScalar_trace ρ l
  rw [hsum] at htrace
  calc ∑ x ∈ (ConjClasses.carrier l).toFinset, ρ.character x * ρ.character x⁻¹
    = ∑ _x ∈ (ConjClasses.carrier l).toFinset,
      (ρ.character (classRep l) * ρ.character (classRep l)⁻¹) :=
      Finset.sum_congr rfl h1
    _ = ((ConjClasses.carrier l).toFinset.card : ℂ)
      * (ρ.character (classRep l) * ρ.character (classRep l)⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Module.finrank ℂ V : ℂ)
      * (centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
      have h2 : ((ConjClasses.carrier l).toFinset.card : ℂ)
        * ρ.character (classRep l)
        = centralScalar ρ l * Module.finrank ℂ V := htrace.symm
      linear_combination h2 * ρ.character (classRep l)⁻¹

end BurnsidePaqb

namespace BurnsidePaqb

/--
[degree_dvd_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/DegreeDivides.lean)
-/
@[path]
lemma degree_dvd_card
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ] :
-- imply
  Module.finrank ℂ V ∣ Fintype.card G := by
-- proof
  classical
  have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
  have hdC : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hST : (Nat.card G : ℂ) = (Module.finrank ℂ V : ℂ) *
    (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
    have hself : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) :=
      self_pair_sum ρ
    have hdecomp := sum_over_classes (fun g => ρ.character g * ρ.character g⁻¹)
    rw [← hself, hdecomp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => class_inner_sum ρ l)
  have hTint : IsIntegral ℤ
    (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) :=
    IsIntegral.sum _ (fun l _ =>
      (centralScalar_isIntegral ρ l).mul (character_isIntegral ρ _))
  have hdiv : (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹)
    = (Nat.card G : ℂ) / (Module.finrank ℂ V : ℂ) := by
    have h1 : (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹)
      * (Module.finrank ℂ V : ℂ) = (Nat.card G : ℂ) := by
      rwa [mul_comm]
    exact (eq_div_iff hdC).mpr h1
  set q : ℚ := (Nat.card G : ℚ) / (Module.finrank ℂ V : ℚ) with hqdef
  have hqC : ((q : ℚ) : ℂ)
    = (∑ l : ConjClasses G, centralScalar ρ l * ρ.character (classRep l)⁻¹) := by
    rw [hqdef]
    push_cast
    exact hdiv.symm
  have hqintC : IsIntegral ℤ ((q : ℚ) : ℂ) := by
    rwa [hqC]
  have : IsScalarTower ℤ ℚ ℂ := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)).mp (by simpa using hqintC)
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hqint
  have hcast : (n : ℚ) = q := by simpa using hn
  have hdq : (Module.finrank ℂ V : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hmul : (n : ℚ) * (Module.finrank ℂ V : ℚ) = (Nat.card G : ℚ) := by
    rw [hcast, hqdef, div_mul_cancel₀ _ hdq]
  have hmulZ : n * (Module.finrank ℂ V : ℤ) = (Nat.card G : ℤ) := by
    exact_mod_cast hmul
  have hdvd : (Module.finrank ℂ V : ℤ) ∣ (Nat.card G : ℤ) :=
    ⟨n, by rw [mul_comm]; exact hmulZ.symm⟩
  have hfin : Module.finrank ℂ V ∣ Nat.card G := Int.natCast_dvd_natCast.mp hdvd
  rwa [Fintype.card_eq_nat_card]

end BurnsidePaqb


-- created on 2026-10-20
-- updated on 2026-10-23

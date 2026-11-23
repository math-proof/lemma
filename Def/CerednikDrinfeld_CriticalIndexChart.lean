import Mathlib
import Lemma.MvPowerSeries.NegV2
import Lemma.MvPowerSeries.CartierModule
import Def.PowerSeries_CartierModuleHomothety
import Lemma.MvPowerSeries.CartierModuleWittAction
import Lemma.MvPowerSeries.CartierModuleBaseChange
import Lemma.MvPowerSeries.SpecialFormalModule
import Lemma.FormalGroup.CartierGradedPiece
import Lemma.MvPolynomial.CartierStructureConstants
import Abbrev.CerednikDrinfeld_CriticalIndexChart

set_option autoImplicit false

noncomputable section

universe u v w

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries

section BaseChange

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
  {B'' : Type w} [CommRing B'']

def cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'')
    (hg : g.comp f = f') : CartierModule p (X.map f).F →+ CartierModule p (X.map f').F :=
  CartierModule.baseChangeEq g (by rw [map_F, map_F, MvFormalGroup.map_map_ringHom, hg])

end BaseChange

namespace CritChart

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

section OneBase

variable [CharP B p]

def IsCritical (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) : Prop :=
  ∀ m ∈ X.gradedPiece j i, ∃ g : CartierModule p X.F, verschiebung g = endAct X.varpiEnd m

def invariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) : AddSubgroup (CartierModule p X.F) where
  carrier := {m | m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m = verschiebung m}
  zero_mem' := ⟨zero_mem _, by rw [map_zero, map_zero]⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, map_add, ha.2, hb.2]⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by rw [map_neg, map_neg, ha.2]⟩

def vPowRange (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ) : AddSubgroup (CartierModule p X.F) where
  carrier := {m | ∃ g ∈ X.gradedPiece j i, (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g = m}
  zero_mem' := ⟨0, zero_mem _, iterate_map_zero _ k⟩
  add_mem' := by
    rintro a b ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
    exact ⟨g + g', add_mem hg hg', iterate_map_add _ k g g'⟩
  neg_mem' := by
    rintro a ⟨g, hg, rfl⟩
    exact ⟨-g, neg_mem hg, iterate_map_neg _ k g⟩

def preInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    AddSubgroup (CartierModule p X.F) where
  carrier := {m | m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m - verschiebung m ∈ vPowRange X j i (2 * n + 1)}
  zero_mem' := ⟨zero_mem _, by rw [map_zero, map_zero, sub_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, by
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by
    rw [map_neg, map_neg, ← neg_sub', sub_eq_add_neg]
    exact neg_mem ha.2⟩

abbrev truncRel (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) : AddSubgroup ↥(preInvariants X j i n) :=
  (vPowRange X j i (2 * n)).addSubgroupOf (preInvariants X j i n)

abbrev truncInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) : Type u :=
  ↥(preInvariants X j i n) ⧸ truncRel X j i n

abbrev truncMk (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    ↥(preInvariants X j i n) →+ truncInvariants X j i n :=
  QuotientAddGroup.mk' (truncRel X j i n)

def invariantsRed (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    ↥(invariants X j i) →+ truncInvariants X j i n :=
  (truncMk X j i n).comp (AddSubgroup.inclusion (invariants_le_preInvariants X j i n))

end OneBase

section Functor

variable {B₀ : Type u} [CommRing B₀]

abbrev cartierMap (X : FormalODModule p B₀) {B' : Type v} [CommRing B'] [Algebra B₀ B'] {B'' : Type w}
    [CommRing B''] [Algebra B₀ B''] (φ : B' →ₐ[B₀] B'') : cartierObj X B' →+ cartierObj X B'' :=
  X.cartierBaseChange (φ : B' →+* B'') φ.comp_algebraMap

variable {B' : Type v} [CommRing B'] [Algebra B₀ B'] {B'' : Type w} [CommRing B''] [Algebra B₀ B'']

variable [CharP B' p] [CharP B'' p]

def invariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) (φ : B' →ₐ[B₀] B'') :
    ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i) →+
      ↥(invariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i) :=
  ((cartierMap X φ).comp (AddSubgroup.subtype _)).codRestrict _
    fun m => cartierMap_mem_invariants X j i φ m.2

def preInvariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'') :
    ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) →+
      ↥(preInvariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i n) :=
  ((cartierMap X φ).comp (AddSubgroup.subtype _)).codRestrict _
    fun m => cartierMap_mem_preInvariants X j i n φ m.2

def truncMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'') :
    truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n →+
      truncInvariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i n :=
  QuotientAddGroup.map _ _ (preInvariantsMap X j i n φ) fun _ hm =>
    cartierMap_mem_vPowRange X j i (2 * n) φ hm

end Functor

section Transition

variable [CharP B p]

def truncTransition (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    truncInvariants X j i (n + 1) →+ truncInvariants X j i n :=
  QuotientAddGroup.map _ _ (AddSubgroup.inclusion (preInvariants_succ_le X j i n hV))
    fun _ hm => vPowRange_succ_le X j i n hV hm

end Transition

end CritChart

end FormalODModule

end CerednikDrinfeld

end

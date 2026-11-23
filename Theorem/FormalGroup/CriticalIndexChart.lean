module

public import Mathlib
public import Theorem.MvPowerSeries.NegV2
public import Theorem.MvPowerSeries.CartierModule
public import Theorem.PowerSeries.CartierModuleHomothety
public import Theorem.MvPowerSeries.CartierModuleWittAction
public import Theorem.MvPowerSeries.CartierModuleBaseChange
public import Theorem.MvPowerSeries.SpecialFormalModule
public import Theorem.FormalGroup.CartierGradedPiece
public import Theorem.MvPolynomial.CartierStructureConstants
public import Abbrev.CerednikDrinfeld_CriticalIndexChart

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u v w

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries

section BaseChange

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
  {B'' : Type w} [CommRing B'']

public theorem map_F_map (f : B →+* B') (g : B' →+* B'') (X : FormalODModule p B) :
    (X.map f).F.map g = (X.map (g.comp f)).F :=
  MvFormalGroup.map_map_ringHom X.F f g


public theorem toPowerSeries_cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) (l : Fin 2) :
    (X.cartierBaseChange g hg m).toPowerSeries l = MvPowerSeries.map g (m.toPowerSeries l) := rfl


public theorem cartierBaseChange_pi (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (endAct (X.map f).varpiEnd m) =
      endAct (X.map f').varpiEnd (X.cartierBaseChange g hg m) := by
  refine CartierModule.baseChangeEq_endAct g _ (fun i => ?_) m
  subst hg
  rfl


public theorem cartierBaseChange_act (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (a : Zp2 p) (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (endAct ((X.map f).actEnd a) m) =
      endAct ((X.map f').actEnd a) (X.cartierBaseChange g hg m) := by
  refine CartierModule.baseChangeEq_endAct g _ (fun i => ?_) m
  subst hg
  rfl


public theorem cartierBaseChange_verschiebung [CharP B' p] [CharP B'' p] (X : FormalODModule p B)
    {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f')
    (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (verschiebung m) = verschiebung (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_verschiebung g _ m


public theorem cartierBaseChange_verschiebung_iterate [CharP B' p] [CharP B'' p] (X : FormalODModule p B)
    {f : B →+* B'} {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f') (k : ℕ)
    (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg ((⇑(verschiebung (p := p) (Φ := (X.map f).F)))^[k] m) =
      (⇑(verschiebung (p := p) (Φ := (X.map f').F)))^[k] (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_verschiebung_iterate g _ k m


public theorem cartierBaseChange_frobenius (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (frobenius m) = frobenius (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_frobenius g _ m


public theorem cartierBaseChange_homothety (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (b : B') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (homothety b m) = homothety (g b) (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_homothety g _ b m


public theorem cartierBaseChange_smul_witt (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (w : WittVector p B') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g hg (w • m) = (WittVector.map g w) • (X.cartierBaseChange g hg m) :=
  CartierModule.baseChangeEq_smul_witt g _ w m


public theorem tangent_cartierBaseChange (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (m : CartierModule p (X.map f).F) :
    tangent (X.cartierBaseChange g hg m) = fun l => g (tangent m l) :=
  CartierModule.tangent_baseChangeEq g _ m


public theorem cartierBaseChange_mem_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) {f : B →+* B'}
    {f' : B →+* B''} (g : B' →+* B'') (hg : g.comp f = f') (i : ℕ)
    {m : CartierModule p (X.map f).F} (hm : m ∈ (X.map f).gradedPiece (f.comp j) i) :
    X.cartierBaseChange g hg m ∈ (X.map f').gradedPiece (f'.comp j) i := by
  intro c
  rw [← cartierBaseChange_act, hm c, cartierBaseChange_homothety]
  congr 1
  rw [map_pow, ← hg]
  rfl


public theorem cartierBaseChange_id (X : FormalODModule p B) {f : B →+* B'}
    (h : (RingHom.id B').comp f = f) (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange (RingHom.id B') h m = m :=
  CartierModule.baseChangeEq_id _ m


public theorem cartierBaseChange_comp {B₃ : Type*} [CommRing B₃] (X : FormalODModule p B) {f : B →+* B'}
    {f' : B →+* B''} {f'' : B →+* B₃} (g : B' →+* B'') (hg : g.comp f = f') (g' : B'' →+* B₃)
    (hg' : g'.comp f' = f'') (hgg' : (g'.comp g).comp f = f'') (m : CartierModule p (X.map f).F) :
    X.cartierBaseChange g' hg' (X.cartierBaseChange g hg m) = X.cartierBaseChange (g'.comp g) hgg' m :=
  CartierModule.baseChangeEq_baseChangeEq g g' _ _ _ m


public theorem cartierBaseChange_injective (X : FormalODModule p B) {f : B →+* B'} {f' : B →+* B''}
    (g : B' →+* B'') (hg : g.comp f = f') (hinj : Function.Injective g) :
    Function.Injective (X.cartierBaseChange g hg) :=
  CartierModule.baseChangeEq_injective g _ hinj

end BaseChange

namespace CritChart

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

section OneBase

variable [CharP B p]


public theorem mem_invariants_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) (m : CartierModule p X.F) :
    m ∈ invariants X j i ↔ m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m = verschiebung m :=
  Iff.rfl


public theorem invariants_le_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    invariants X j i ≤ X.gradedPiece j i := fun _ hm => hm.1


public theorem mem_vPowRange_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ) (m : CartierModule p X.F) :
    m ∈ vPowRange X j i k ↔
      ∃ g ∈ X.gradedPiece j i, (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g = m :=
  Iff.rfl


public theorem vPowRange_zero (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    vPowRange X j i 0 = X.gradedPiece j i := by
  ext m
  rw [mem_vPowRange_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hm
    exact ⟨m, hm, rfl⟩


public theorem iterate_verschiebung_mem_vPowRange (X : FormalODModule p B) (j : Zp2 p →+* B) (i k : ℕ)
    {g : CartierModule p X.F} (hg : g ∈ X.gradedPiece j i) :
    (⇑(verschiebung (p := p) (Φ := X.F)))^[k] g ∈ vPowRange X j i k :=
  ⟨g, hg, rfl⟩


public theorem mem_preInvariants_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ preInvariants X j i n ↔
      m ∈ X.gradedPiece j i ∧ endAct X.varpiEnd m - verschiebung m ∈ vPowRange X j i (2 * n + 1) :=
  Iff.rfl


public theorem invariants_le_preInvariants (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    invariants X j i ≤ preInvariants X j i n := fun m hm =>
  ⟨hm.1, by rw [hm.2, sub_self]; exact zero_mem _⟩


public theorem preInvariants_le_gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    preInvariants X j i n ≤ X.gradedPiece j i := fun _ hm => hm.1


public theorem truncMk_surjective (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) :
    Function.Surjective (truncMk X j i n) :=
  QuotientAddGroup.mk'_surjective _


public theorem truncMk_eq_zero_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m : ↥(preInvariants X j i n)) :
    truncMk X j i n m = 0 ↔ (m : CartierModule p X.F) ∈ vPowRange X j i (2 * n) := by
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  rfl


public theorem truncMk_eq_truncMk_iff (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (m m' : ↥(preInvariants X j i n)) :
    truncMk X j i n m = truncMk X j i n m' ↔ (m : CartierModule p X.F) - m' ∈ vPowRange X j i (2 * n) := by
  rw [← sub_eq_zero, ← map_sub, truncMk_eq_zero_iff]
  rfl


public theorem truncInvariants_zero_subsingleton (X : FormalODModule p B) (j : Zp2 p →+* B) (i : ℕ) :
    Subsingleton (truncInvariants X j i 0) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := truncMk_surjective X j i 0 a
  obtain ⟨b, rfl⟩ := truncMk_surjective X j i 0 b
  rw [truncMk_eq_truncMk_iff, Nat.mul_zero, vPowRange_zero]
  exact sub_mem a.2.1 b.2.1


public theorem invariantsRed_apply (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ) (m : ↥(invariants X j i)) :
    invariantsRed X j i n m = truncMk X j i n (AddSubgroup.inclusion (invariants_le_preInvariants X j i n) m) :=
  rfl

end OneBase

section Functor

variable {B₀ : Type u} [CommRing B₀]


public theorem cartierMap_id (X : FormalODModule p B₀) (m : cartierObj X B') : cartierMap X (AlgHom.id B₀ B') m = m :=
  X.cartierBaseChange_id _ m


public theorem cartierMap_comp (X : FormalODModule p B₀) {B₃ : Type*} [CommRing B₃] [Algebra B₀ B₃]
    (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃) (m : cartierObj X B') :
    cartierMap X ψ (cartierMap X φ m) = cartierMap X (ψ.comp φ) m :=
  X.cartierBaseChange_comp _ _ _ _ _ m

variable [CharP B' p] [CharP B'' p]


public theorem cartierMap_mem_invariants (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) (φ : B' →ₐ[B₀] B'')
    {m : cartierObj X B'} (hm : m ∈ invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i) :
    cartierMap X φ m ∈ invariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i := by
  refine ⟨X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hm.1, ?_⟩
  rw [cartierMap, ← cartierBaseChange_pi, hm.2, cartierBaseChange_verschiebung]


public theorem cartierMap_mem_vPowRange (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i k : ℕ) (φ : B' →ₐ[B₀] B'')
    {m : cartierObj X B'} (hm : m ∈ vPowRange (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i k) :
    cartierMap X φ m ∈ vPowRange (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i k := by
  obtain ⟨g, hg, rfl⟩ := hm
  exact ⟨cartierMap X φ g, X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hg,
    (X.cartierBaseChange_verschiebung_iterate φ.toRingHom φ.comp_algebraMap k g).symm⟩


public theorem cartierMap_mem_preInvariants (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (φ : B' →ₐ[B₀] B'') {m : cartierObj X B'}
    (hm : m ∈ preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    cartierMap X φ m ∈ preInvariants (X.map (algebraMap B₀ B'')) ((algebraMap B₀ B'').comp j) i n := by
  refine ⟨X.cartierBaseChange_mem_gradedPiece j φ.toRingHom φ.comp_algebraMap i hm.1, ?_⟩
  have h := cartierMap_mem_vPowRange X j i (2 * n + 1) φ hm.2
  rwa [map_sub, cartierMap, cartierBaseChange_pi, cartierBaseChange_verschiebung] at h


@[simp] public theorem coe_invariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) (φ : B' →ₐ[B₀] B'')
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    (invariantsMap X j i φ m : cartierObj X B'') = cartierMap X φ m := rfl


@[simp] public theorem coe_preInvariantsMap (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (φ : B' →ₐ[B₀] B'') (m : ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n)) :
    (preInvariantsMap X j i n φ m : cartierObj X B'') = cartierMap X φ m := rfl


public theorem truncMap_truncMk (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'')
    (m₀ : ↥(preInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n)) :
    truncMap X j i n φ (truncMk _ _ i n m₀) = truncMk _ _ i n (preInvariantsMap X j i n φ m₀) :=
  rfl


public theorem truncMap_invariantsRed (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) (φ : B' →ₐ[B₀] B'')
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    truncMap X j i n φ (invariantsRed _ _ i n m) = invariantsRed _ _ i n (invariantsMap X j i φ m) :=
  rfl

omit [CharP B'' p] in


public theorem invariantsMap_id (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ)
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    invariantsMap X j i (AlgHom.id B₀ B') m = m :=
  Subtype.ext (cartierMap_id X m.1)


public theorem invariantsMap_comp (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i : ℕ) {B₃ : Type*}
    [CommRing B₃] [Algebra B₀ B₃] [CharP B₃ p] (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃)
    (m : ↥(invariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i)) :
    invariantsMap X j i ψ (invariantsMap X j i φ m) = invariantsMap X j i (ψ.comp φ) m :=
  Subtype.ext (cartierMap_comp X φ ψ m.1)

omit [CharP B'' p] in


public theorem truncMap_id (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ)
    (x : truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    truncMap X j i n (AlgHom.id B₀ B') x = x := by
  obtain ⟨m, rfl⟩ := truncMk_surjective _ _ i n x
  exact (truncMap_truncMk X j i n _ m).trans (congrArg _ (Subtype.ext (cartierMap_id X m.1)))


public theorem truncMap_comp (X : FormalODModule p B₀) (j : Zp2 p →+* B₀) (i n : ℕ) {B₃ : Type*}
    [CommRing B₃] [Algebra B₀ B₃] [CharP B₃ p] (φ : B' →ₐ[B₀] B'') (ψ : B'' →ₐ[B₀] B₃)
    (x : truncInvariants (X.map (algebraMap B₀ B')) ((algebraMap B₀ B').comp j) i n) :
    truncMap X j i n ψ (truncMap X j i n φ x) = truncMap X j i n (ψ.comp φ) x := by
  obtain ⟨m, rfl⟩ := truncMk_surjective _ _ i n x
  exact congrArg (truncMk _ _ i n) (Subtype.ext (cartierMap_comp X φ ψ m.1))

end Functor

section Transition

variable [CharP B p]


public theorem preInvariants_succ_le (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    preInvariants X j i (n + 1) ≤ preInvariants X j i n := by
  intro m hm
  refine ⟨hm.1, ?_⟩
  obtain ⟨g, hg, hgm⟩ := hm.2
  refine ⟨verschiebung (verschiebung g), hV g hg, ?_⟩
  rw [← hgm, show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring,
    Function.iterate_add_apply (⇑(verschiebung (p := p) (Φ := X.F))) (2 * n + 1) 2 g]
  rfl


public theorem vPowRange_succ_le (X : FormalODModule p B) (j : Zp2 p →+* B) (i n : ℕ)
    (hV : ∀ g ∈ X.gradedPiece j i, verschiebung (verschiebung g) ∈ X.gradedPiece j i) :
    vPowRange X j i (2 * (n + 1)) ≤ vPowRange X j i (2 * n) := by
  rintro m ⟨g, hg, hgm⟩
  refine ⟨verschiebung (verschiebung g), hV g hg, ?_⟩
  rw [← hgm, show 2 * (n + 1) = 2 * n + 2 by ring,
    Function.iterate_add_apply (⇑(verschiebung (p := p) (Φ := X.F))) (2 * n) 2 g]
  rfl


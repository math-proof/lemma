import Mathlib
import sympy.Basic
open Polynomial IsLocalRing


private lemma standardEtalePair_residueSection_exists
  {R : Type u}
  [CommRing R]
  [HenselianLocalRing R]
  (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
  ∃ ret : P.Ring →ₐ[R] R,
    ∀ s : P.Ring, algebraMap R (ResidueField R) (ret s) = φ s := by
  have aeval_eq : ∀ (r : R) (p : R[X]), aeval r p = p.eval r :=
    fun r p => congrFun (coe_aeval_eq_eval r) p
  have hx₀ : P.HasMap (φ P.X) := StandardEtalePair.hasMap_X.map φ
  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := R) (φ P.X)
  have ha₀' : algebraMap R (ResidueField R) a₀ = φ P.X := by
    rwa [ResidueField.algebraMap_eq]
  have hresAt : ∀ b : R, algebraMap R (ResidueField R) b = φ P.X →
      ∀ p : R[X], algebraMap R (ResidueField R) (p.eval b) = aeval (φ P.X) p := by
    intro b hb p
    rw [← aeval_algebraMap_apply_eq_algebraMap_eval, hb]
  have unitOfRes : ∀ b : R, IsUnit (algebraMap R (ResidueField R) b) → IsUnit b := by
    intro b hb
    rw [← notMem_maximalIdeal]
    intro hbm
    exact hb.ne_zero (by rw [ResidueField.algebraMap_eq]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hbm)
  have hmem : P.f.eval a₀ ∈ maximalIdeal R := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    show algebraMap R (ResidueField R) (P.f.eval a₀) = 0
    rw [hresAt a₀ ha₀']
    apply hx₀.1
  have hud : IsUnit ((derivative P.f).eval a₀) :=
    unitOfRes _ (hresAt a₀ ha₀' _ ▸ hx₀.isUnit_derivative_f)
  obtain ⟨a, haroot, hadiff⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a₀ hmem hud
  have hares : algebraMap R (ResidueField R) a = φ P.X := by
    rw [ResidueField.algebraMap_eq, ← ha₀]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a a₀).mpr hadiff
  have hmap : P.HasMap a := ⟨aeval_eq a P.f ▸ haroot,
    aeval_eq a _ ▸ unitOfRes _ (hresAt a hares _ ▸ hx₀.2)⟩
  refine ⟨P.lift a hmap, fun s => ?_⟩
  have hcomp : (Algebra.ofId R (ResidueField R)).comp (P.lift a hmap) = φ :=
    StandardEtalePair.hom_ext (by rwa [AlgHom.comp_apply, StandardEtalePair.lift_X, Algebra.ofId_apply])
  have hs := AlgHom.congr_fun hcomp s
  rwa [AlgHom.comp_apply, Algebra.ofId_apply] at hs

private lemma isStandardEtale_residueSection_exists
  {R : Type u}
  [CommRing R]
  [HenselianLocalRing R]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
  (φ : S →ₐ[R] ResidueField R) :
  ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  obtain ⟨Pres⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  obtain ⟨ret, hret⟩ :=
    standardEtalePair_residueSection_exists Pres.P (φ.comp Pres.equivRing.symm.toAlgHom)
  refine ⟨ret.comp Pres.equivRing.toAlgHom, fun s => ?_⟩
  have := hret (Pres.equivRing s)
  simpa using this

private lemma etale_residueSection_exists_of_henselianLocalRing
  {R : Type u}
  [CommRing R]
  [HenselianLocalRing R]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra.Etale R S]
  (φ : S →ₐ[R] ResidueField R) :
  ∃ ret : S →ₐ[R] R, ∀ s : S, algebraMap R (ResidueField R) (ret s) = φ s := by
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
  have : Algebra.IsEtaleAt R (RingHom.ker φ.toRingHom) := inferInstance
  obtain ⟨g, hg, hSE⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := S) (RingHom.ker φ.toRingHom)
  let := hSE
  have hu : IsUnit (φ.toRingHom g) :=
    isUnit_iff_ne_zero.mpr fun h0 => hg (RingHom.mem_ker.mpr h0)
  have hlift : ∀ s : S,
      IsLocalization.Away.lift (S := Localization.Away g) g hu
        (algebraMap S (Localization.Away g) s) = φ.toRingHom s :=
    fun s => IsLocalization.Away.lift_eq (S := Localization.Away g) g hu s
  let ψ : Localization.Away g →ₐ[R] ResidueField R :=
    { toRingHom := IsLocalization.Away.lift (S := Localization.Away g) g hu
      commutes' := fun r => by
        show IsLocalization.Away.lift (S := Localization.Away g) g hu
          (algebraMap R (Localization.Away g) r) = algebraMap R (ResidueField R) r
        rw [IsScalarTower.algebraMap_apply R S (Localization.Away g), hlift (algebraMap R S r)]
        exact φ.commutes r }
  obtain ⟨ret, hret⟩ := isStandardEtale_residueSection_exists (Localization.Away g) ψ
  refine ⟨ret.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), fun s => ?_⟩
  rw [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    hret (algebraMap S (Localization.Away g) s)]
  exact hlift s
/--
[HenselianLocalRing_exists_algHom_lift_of_etale](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HenselianLocalRing_exists_algHom_lift_of_etale.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [HenselianLocalRing R]
  {S : Type u} [CommRing S] [Algebra R S] [Algebra.Etale R S]
  {φ : S →ₐ[R] IsLocalRing.ResidueField R} :
-- imply
  ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s :=
-- proof
  etale_residueSection_exists_of_henselianLocalRing S φ


-- created on 2026-10-23

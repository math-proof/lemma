import Mathlib
import sympy.Basic
import Lemma.NeronModelInfra.TopFormOrder


namespace Definitions
end Definitions
open Definitions
open NeronModelInfra NeronModelInfra.TopFormOrder
set_option backward.isDefEq.respectTransparency false


/-- ported from external source -/
private lemma orderEmbedding_fin_eq_id
  {d : ℕ}
  (f : Fin d ↪o Fin d) :
  (f : Fin d → Fin d) = id := by
  have hs : Function.Surjective f := Finite.surjective_of_injective f.injective
  have h1 : Set.range (f : Fin d → Fin d) = Set.range (id : Fin d → Fin d) := by
    rw [Set.range_id, Set.range_eq_univ.mpr hs]
  refine (f.strictMono.range_inj_of_wellFoundedLT strictMono_id).mp h1

private lemma exists_smul_of_exteriorBasis
  {A M : Type u}
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  (d : ℕ)
  (b : Module.Basis (Fin d) A M)
  (η : ExteriorAlgebra.exteriorPower A d M) :
  ∃ c : A, η = c • exteriorPower.ιMulti A d b := by
  classical
  let B := b.exteriorPower d
  let s₀ : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  have hs : ∀ s : Set.powersetCard (Fin d) d, s = s₀ := by
    intro s
    apply Subtype.ext
    show s.val = Finset.univ
    exact Finset.eq_univ_of_card s.val (by rw [Fintype.card_fin]; apply s.prop)
  have hB : B s₀ = exteriorPower.ιMulti A d b := by
    rw [show B s₀ = exteriorPower.ιMulti_family A d b s₀ from exteriorPower.basis_apply A d b s₀]
    unfold exteriorPower.ιMulti_family
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s₀ : Fin d ↪o Fin d) i) = b i
    rw [orderEmbedding_fin_eq_id]
    rfl
  refine ⟨B.repr η s₀, ?_⟩
  rw [← hB]
  conv_lhs => rw [← B.sum_repr η]
  rw [Fintype.sum_eq_single s₀ (fun s hs' => absurd (hs s) hs')]

private lemma smul_exteriorBasis_injective
  {A M : Type u}
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  (d : ℕ)
  (b : Module.Basis (Fin d) A M)
  (c c' : A)
  (hc : c • exteriorPower.ιMulti A d b = c' • exteriorPower.ιMulti A d b) :
  c = c' := by
  classical
  let B := b.exteriorPower d
  let s₀ : Set.powersetCard (Fin d) d := ⟨Finset.univ, by simp [Set.powersetCard]⟩
  have hs : ∀ s : Set.powersetCard (Fin d) d, s = s₀ := by
    intro s
    apply Subtype.ext
    show s.val = Finset.univ
    exact Finset.eq_univ_of_card s.val (by rw [Fintype.card_fin]; apply s.prop)
  have hB : B s₀ = exteriorPower.ιMulti A d b := by
    rw [show B s₀ = exteriorPower.ιMulti_family A d b s₀ from exteriorPower.basis_apply A d b s₀]
    unfold exteriorPower.ιMulti_family
    congr 1
    funext i
    show b ((Set.powersetCard.ofFinEmbEquiv.symm s₀ : Fin d ↪o Fin d) i) = b i
    rw [orderEmbedding_fin_eq_id]
    rfl
  rw [← hB] at hc
  have h := congrArg (fun x => B.repr x s₀) hc
  simpa [B.repr_self] using h

private lemma helper_main
  (K : Type u) [Field K]
  (A : Type u) [CommRing A] [Algebra K A]
  (F : Type u) [Field F] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
  (M : Submonoid A) [IsLocalization M F]
  (d : ℕ)
  (b : Module.Basis (Fin d) A Ω[A⁄K])
  (ω : ExteriorAlgebra.exteriorPower A d Ω[A⁄K])
  (hω : Function.Bijective fun g : A => g • ω) :
  topFormMap K K A F d ω ≠ 0 := by
  classical
  let instA := moduleAlong A F (ExteriorAlgebra.exteriorPower F d Ω[F⁄K])
  have : IsScalarTower A F (ExteriorAlgebra.exteriorPower F d Ω[F⁄K]) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨c, hc⟩ := exists_smul_of_exteriorBasis d b ω
  obtain ⟨g, hg⟩ := hω.2 (exteriorPower.ιMulti A d b)
  have hgc : g * c = 1 :=
    smul_exteriorBasis_injective d b _ _ (by rwa [mul_smul, ← hc, one_smul])
  have hcU : IsUnit c := IsUnit.of_mul_eq_one g (by rwa [mul_comm])
  set v : Fin d → Ω[F⁄K] := fun i => KaehlerDifferential.map K K A F (b i) with hv
  have hρ : topFormMap K K A F d (exteriorPower.ιMulti A d b) = exteriorPower.ιMulti F d v := by
    show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K A F d) (exteriorPower.ιMulti A d b) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  have : IsLocalizedModule M (KaehlerDifferential.map K K A F) :=
    KaehlerDifferential.isLocalizedModule_map K A F M
  let bF : Module.Basis (Fin d) F Ω[F⁄K] :=
    b.ofIsLocalizedModule F M (KaehlerDifferential.map K K A F)
  have hbF : (bF : Fin d → Ω[F⁄K]) = v := by
    funext i
    simp only [bF, Module.Basis.ofIsLocalizedModule_apply, hv]
  have hω' : topFormMap K K A F d ω = algebraMap A F c • exteriorPower.ιMulti F d v := by
    rw [hc, LinearMap.map_smul, hρ, algebraMap_smul]
  rw [hω']
  intro h0
  have hsmul : algebraMap A F c • exteriorPower.ιMulti F d bF = 0 := by
    rw [show (bF : Fin d → Ω[F⁄K]) = v from hbF, h0]
  have := smul_exteriorBasis_injective d bF (algebraMap A F c) 0 (by rw [hsmul, zero_smul])
  exact (hcU.map (algebraMap A F)).ne_zero this

@[path]
private lemma main
  {K : Type u} [Field K]
  {A : Type u} [CommRing A] [Algebra K A]
  {F : Type u} [Field F] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
  {M : Submonoid A} [IsLocalization M F]
  {d : ℕ}
  {b : Module.Basis (Fin d) A Ω[A⁄K]}
  {ω : ExteriorAlgebra.exteriorPower A d Ω[A⁄K]}
-- given
  (hω : Function.Bijective fun g : A => g • ω) :
-- imply
  NeronModelInfra.TopFormOrder.topFormMap K K A F d ω ≠ 0 :=
-- proof
  helper_main K A F M d b ω hω


-- created on 2026-10-24

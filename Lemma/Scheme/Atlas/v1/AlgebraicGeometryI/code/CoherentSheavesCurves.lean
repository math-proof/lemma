import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
open scoped TensorProduct


/--
[Submodule.le_saturation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma Submodule.le_saturation
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  N ≤ N.saturation := by
-- proof
  intro x hx
  simp only [saturation, Submodule.mem_comap]
  have : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hx
  rw [this]; exact zero_mem _

/--
[Submodule.saturation_map_mkQ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma Submodule.saturation_map_mkQ
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  Submodule.map N.mkQ N.saturation = Submodule.torsion R (M ⧸ N) := by
-- proof
  simp only [saturation, Submodule.map_comap_eq, Submodule.range_mkQ, top_inf_eq]

/--
[isTorsionFree_of_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma isTorsionFree_of_linearEquiv
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [AddCommGroup P]
  [Module R N]
  [Module R P]
  {e : N ≃ₗ[R] P}
-- given
  (h : Module.IsTorsionFree R N) :
-- imply
  Module.IsTorsionFree R P := by
-- proof
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot] at h ⊢
  ext x
  simp only [Submodule.mem_bot, Submodule.mem_torsion_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, hax⟩
    have hmem : e.symm x ∈ Submodule.torsion R N := by
      rw [Submodule.mem_torsion_iff]
      refine ⟨⟨a, ha⟩, ?_⟩
      show a • e.symm x = 0
      have hax' : a • x = 0 := hax
      simp [← e.symm.map_smul, hax']
    rw [h, Submodule.mem_bot] at hmem
    exact e.symm.injective (by rw [hmem, map_zero])
  · rintro rfl
    exact ⟨⟨1, Submonoid.one_mem _⟩, by simp⟩

/--
[Submodule.quotient_saturation_isTorsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma Submodule.quotient_saturation_isTorsionFree
  [CommRing R]
  [IsDomain R]
  [AddCommGroup M]
  [Module R M]
  {N : Submodule R M} :
-- imply
  Module.IsTorsionFree R (M ⧸ N.saturation) := by
-- proof
  have h_le : N ≤ N.saturation := N.le_saturation
  let e₁ := Submodule.quotientQuotientEquivQuotient N N.saturation h_le
  have hmap : Submodule.map N.mkQ N.saturation = Submodule.torsion R (M ⧸ N) :=
    N.saturation_map_mkQ
  let e₂ := Submodule.Quotient.equiv (Submodule.torsion R (M ⧸ N))
    (Submodule.map N.mkQ N.saturation)
    (LinearEquiv.refl R (M ⧸ N))
    (by simp [hmap])
  exact isTorsionFree_of_linearEquiv (e₂ ≪≫ₗ e₁) Submodule.QuotientTorsion.instIsTorsionFree
section Rank
variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

/--
[CoherentSheavesCurves.sheafRank_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.sheafRank_additive
  {R : Type*}
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [Module R A]
  [Module R B]
  [Module R C]
  {f : A →ₗ[R] B}
  {g : B →ₗ[R] C}
  {H : Function.Exact f g}
  [Module.Flat R K]
  [FiniteDimensional K (K ⊗[R] B)]
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g) :
-- imply
  CoherentSheavesCurves.sheafRank R K B = CoherentSheavesCurves.sheafRank R K A + CoherentSheavesCurves.sheafRank R K C := by
-- proof
  unfold CoherentSheavesCurves.sheafRank
  let f' : K ⊗[R] A →ₗ[K] K ⊗[R] B := f.baseChange K
  let g' : K ⊗[R] B →ₗ[K] K ⊗[R] C := g.baseChange K
  have hf'_fun : ⇑f' = ⇑(f.lTensor K) := (LinearMap.baseChange_eq_ltensor f).symm
  have hg'_fun : ⇑g' = ⇑(g.lTensor K) := (LinearMap.baseChange_eq_ltensor g).symm
  have hinj : Function.Injective f' := by
    rw [Function.Injective, hf'_fun]
    exact fun _ _ h => Module.Flat.lTensor_preserves_injective_linearMap f hf h
  have hsurj : Function.Surjective g' := by
    intro x; rw [hg'_fun]; exact (LinearMap.lTensor_surjective K hg) x
  have hexact : Function.Exact f' g' := by
    intro x; rw [hf'_fun, hg'_fun]; exact (Module.Flat.lTensor_exact K H) x
  haveI : Module.Finite K (K ⊗[R] A) := Module.Finite.of_injective f' hinj
  haveI : Module.Finite K (K ⊗[R] C) := Module.Finite.of_surjective g' hsurj
  have hlen := Module.length_eq_add_of_exact f' g' hinj hsurj hexact
  rw [Module.length_eq_finrank K, Module.length_eq_finrank K, Module.length_eq_finrank K] at hlen
  have : (Module.finrank K (K ⊗[R] B) : ℕ∞) =
    ↑(Module.finrank K (K ⊗[R] A) + Module.finrank K (K ⊗[R] C)) := by
    rw [hlen, Nat.cast_add]
  exact WithTop.coe_injective this

/--
[CoherentSheavesCurves.sheafRank_additive_fractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.sheafRank_additive_fractionRing
  {R : Type*}
  [CommRing R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [Module R A]
  [Module R B]
  [Module R C]
  {f : A →ₗ[R] B}
  {g : B →ₗ[R] C}
  {H : Function.Exact f g}
  [FiniteDimensional K (K ⊗[R] B)]
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g) :
-- imply
  CoherentSheavesCurves.sheafRank R K B = CoherentSheavesCurves.sheafRank R K A + CoherentSheavesCurves.sheafRank R K C := by
-- proof
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  exact CoherentSheavesCurves.sheafRank_additive R K f g hf hg H
end Rank
section GrothendieckGroup

/--
[CoherentSheavesCurves.K0.ses_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.K0.ses_relation
  {R : Type*}
  [Ring R]
  {A B C : ModuleCat R}
  {f : A →ₗ[R] B}
  {g : B →ₗ[R] C}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hex : Function.Exact f g) :
-- imply
  CoherentSheavesCurves.K0.classOf R B = CoherentSheavesCurves.K0.classOf R A + CoherentSheavesCurves.K0.classOf R C :=
-- proof
  DegreeAdditivity.GrothendieckGroupK0.ses_relation R f g hf hg hex

/--
[CoherentSheavesCurves.K0.classOf_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.K0.classOf_iso
  {R : Type*}
  [Ring R]
  {M N : ModuleCat R}
  {e : M ≃ₗ[R] N} :
-- imply
  CoherentSheavesCurves.K0.classOf R M = CoherentSheavesCurves.K0.classOf R N :=
-- proof
  DegreeAdditivity.GrothendieckGroupK0.classOf_iso R M N e

/--
[CoherentSheavesCurves.K0.classOf_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.K0.classOf_prod
  {R : Type*}
  [Ring R]
  {M N : ModuleCat R} :
-- imply
  CoherentSheavesCurves.K0.classOf R (ModuleCat.of R (M × N)) = CoherentSheavesCurves.K0.classOf R M + CoherentSheavesCurves.K0.classOf R N :=
-- proof
  DegreeAdditivity.GrothendieckGroupK0.classOf_prod R M N

/--
[CoherentSheavesCurves.K0.lift_classOf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.K0.lift_classOf
  {R : Type*}
  [Ring R]
  [AddCommGroup G]
  {φ : ModuleCat R → G}
  {M : ModuleCat R}
-- given
  (hφ : DegreeAdditivity.IsSESAdditive R φ) :
-- imply
  CoherentSheavesCurves.K0.lift R φ hφ (CoherentSheavesCurves.K0.classOf R M) = φ M :=
-- proof
  DegreeAdditivity.GrothendieckGroupK0.lift_classOf R φ hφ M

/--
[CoherentSheavesCurves.K0.lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.K0.lift_unique
  {R : Type*}
  [Ring R]
  [AddCommGroup G]
  {ψ₁ ψ₂ : CoherentSheavesCurves.K0 R →+ G}
-- given
  (h : ∀ M : ModuleCat R, ψ₁ (CoherentSheavesCurves.K0.classOf R M) = ψ₂ (CoherentSheavesCurves.K0.classOf R M)) :
-- imply
  ψ₁ = ψ₂ :=
-- proof
  DegreeAdditivity.GrothendieckGroupK0.lift_unique R ψ₁ ψ₂ h

/--
[CoherentSheavesCurves.degree_additive_ses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.degree_additive_ses
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [Module R A]
  [Module R B]
  [Module R C]
  {f : A →ₗ[R] B}
  {g : B →ₗ[R] C}
  {H : Function.Exact f g}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g) :
-- imply
  CoherentSheavesCurves.degree R B = CoherentSheavesCurves.degree R A + CoherentSheavesCurves.degree R C :=
-- proof
Module.length_eq_add_of_exact f g hf hg H

/--
[CoherentSheavesCurves.lemma34](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.lemma34
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup E]
  [AddCommGroup E']
  [AddCommGroup T]
  [Module R E]
  [Module R E']
  [Module R T]
  {f : E →ₗ[R] E'}
  {g : E' →ₗ[R] T}
  {H : Function.Exact f g}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g) :
-- imply
  CoherentSheavesCurves.degree R E' = CoherentSheavesCurves.degree R E + CoherentSheavesCurves.degree R T :=
-- proof
  Module.length_eq_add_of_exact f g hf hg H

/--
[CoherentSheavesCurves.degree_le_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.degree_le_of_injective
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup A]
  [AddCommGroup B]
  [Module R A]
  [Module R B]
  {f : A →ₗ[R] B}
-- given
  (hf : Function.Injective f) :
-- imply
  CoherentSheavesCurves.degree R A ≤ CoherentSheavesCurves.degree R B :=
-- proof
  Module.length_le_of_injective f hf

/--
[CoherentSheavesCurves.degree_le_of_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.degree_le_of_surjective
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup A]
  [AddCommGroup B]
  [Module R A]
  [Module R B]
  {f : A →ₗ[R] B}
-- given
  (hf : Function.Surjective f) :
-- imply
  CoherentSheavesCurves.degree R B ≤ CoherentSheavesCurves.degree R A :=
-- proof
  Module.length_le_of_surjective f hf

/--
[CoherentSheavesCurves.degree_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.degree_eq_finrank
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {K : Type*}
  [DivisionRing K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [Module.Finite K V] :
-- imply
  CoherentSheavesCurves.degree K V = Module.finrank K V :=
-- proof
  Module.length_eq_finrank K V

/--
[CoherentSheavesCurves.degree_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.degree_prod
  [Ring R]
  [AddCommGroup M]
  [Module R M]
  {R : Type*}
  [Ring R]
  {M N : Type*}
  [AddCommGroup M]
  [AddCommGroup N]
  [Module R M]
  [Module R N] :
-- imply
  CoherentSheavesCurves.degree R (M × N) = CoherentSheavesCurves.degree R M + CoherentSheavesCurves.degree R N := by
-- proof
  exact Module.length_prod R M N
section TorsionRank
variable {R : Type*} [CommRing R] [IsDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
[CoherentSheavesCurves.sheafRank_of_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma CoherentSheavesCurves.sheafRank_of_torsion
  [CommRing R]
  [IsDomain R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  [AddCommGroup M]
  [Module R M]
-- given
  (hM : Module.IsTorsion R M) :
-- imply
  CoherentSheavesCurves.sheafRank R K M = 0 := by
-- proof
  unfold CoherentSheavesCurves.sheafRank
  have hsub : Subsingleton (K ⊗[R] M) := by
    constructor
    intro x y
    suffices h : ∀ z : K ⊗[R] M, z = 0 by rw [h x, h y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul k m =>
      obtain ⟨⟨r, hr⟩, hrm⟩ := @hM m
      have hr_ne : r ≠ 0 := nonZeroDivisors.ne_zero hr
      have hrm' : r • m = 0 := by simpa using hrm
      have h1 : (r • k) ⊗ₜ[R] m = k ⊗ₜ[R] (r • m) := TensorProduct.smul_tmul r k m
      rw [show r • k = algebraMap R K r * k from Algebra.smul_def r k] at h1
      have h2 : (algebraMap R K r * k) ⊗ₜ[R] m = (0 : K ⊗[R] M) := by
        rw [h1, hrm', TensorProduct.tmul_zero]
      have halg_ne : algebraMap R K r ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
      calc k ⊗ₜ[R] m
        = ((algebraMap R K r)⁻¹ * (algebraMap R K r)) • k ⊗ₜ[R] m := by
          rw [inv_mul_cancel₀ halg_ne, one_smul]
        _ = ((algebraMap R K r)⁻¹ * (algebraMap R K r * k)) ⊗ₜ[R] m := by
          rw [mul_smul]; rfl
        _ = (algebraMap R K r)⁻¹ • ((algebraMap R K r * k) ⊗ₜ[R] m) := by
          rw [TensorProduct.smul_tmul']; simp
        _ = 0 := by rw [h2, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact @Module.finrank_zero_of_subsingleton K (K ⊗[R] M) _ _ _ _ hsub
end TorsionRank
section DegreeViaDeterminant
variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/--
[noZeroSMulDivisors_of_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean)
-/
@[path]
lemma noZeroSMulDivisors_of_linearEquiv
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [CommRing R']
  [IsDomain R']
  [AddCommGroup M₁]
  [Module R' M₁]
  [AddCommGroup M₂]
  [Module R' M₂]
  [NoZeroSMulDivisors R' M₂]
  {e : M₁ ≃ₗ[R'] M₂} :
-- imply
  NoZeroSMulDivisors R' M₁ where eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
-- proof
  have h' : r • e x = 0 := by rw [← e.map_smul, h, map_zero]
  obtain hr | hx := smul_eq_zero.mp h'
  · left; exact hr
  · right; exact e.injective (by rw [hx, map_zero])
/-- The degree of a finite torsion-free module over a Dedekind domain, defined via the
determinant invertible-ideal construction. -/
end DegreeViaDeterminant


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


private lemma injective_sq_sub_mul_of_forall_joint_eigenvector
  [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (c : K) (A B : Module.End K W) (hAB : Commute A B)
  (h : ∀ (v : W) (a b : K), v ≠ 0 → A v = a • v → B v = b • v → a * b ≠ c ^ 2) :
-- imply
  Function.Injective (c ^ 2 • (1 : Module.End K W) - A * B) := by
-- proof
  classical
  set S : Module.End K W := c ^ 2 • (1 : Module.End K W) - A * B with hS
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  have hSA : Commute A S := by
    rw [hS]; exact ((Commute.one_right A).smul_right _).sub_right ((Commute.refl A).mul_right hAB)
  have hSB : Commute B S := by
    rw [hS]; exact ((Commute.one_right B).smul_right _).sub_right (hAB.symm.mul_right (Commute.refl B))
  let U := LinearMap.ker S
  have hUA : Set.MapsTo A U U := fun v hv => by
    show S (A v) = 0
    rw [← Module.End.mul_apply, ← hSA.eq, Module.End.mul_apply, show S v = 0 from hv, map_zero]
  have hUB : Set.MapsTo B U U := fun v hv => by
    show S (B v) = 0
    rw [← Module.End.mul_apply, ← hSB.eq, Module.End.mul_apply, show S v = 0 from hv, map_zero]
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hker
  let AU : Module.End K U := A.restrict hUA
  let BU : Module.End K U := B.restrict hUB
  have hcommU : Commute AU BU := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    exact LinearMap.congr_fun hAB.eq (v : W)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue AU
  let E := AU.eigenspace a
  have hEB : Set.MapsTo BU E E := by
    have := Module.End.mapsTo_genEigenspace_of_comm hcommU a 1
    simpa using this
  have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.2 (Module.End.hasEigenvalue_iff.1 ha)
  obtain ⟨b, hb⟩ := Module.End.exists_eigenvalue (BU.restrict hEB)
  obtain ⟨y, hy⟩ := hb.exists_hasEigenvector
  set w : W := ((y : U) : W) with hw
  have hw0 : w ≠ 0 := by
    intro h0; apply hy.2; ext; exact h0
  have hAw : A w = a • w := by
    have h1 : AU (y : U) = a • (y : U) := Module.End.mem_eigenspace_iff.1 y.2
    refine congrArg Subtype.val h1
  have hBw : B w = b • w := by
    have h2 : BU (y : U) = b • (y : U) := congrArg Subtype.val hy.apply_eq_smul
    refine congrArg Subtype.val h2
  have hSw : S w = 0 := (y : U).2
  have key : S w = (c ^ 2 - a * b) • w := by
    rw [hS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, hBw, map_smul, hAw]
    module
  have : (c ^ 2 - a * b) • w = 0 := by rw [← key, hSw]
  obtain h0 | h0 := smul_eq_zero.1 this
  · exact h w a b hw0 hAw hBw (by linear_combination -h0)
  · exact hw0 h0

private lemma injective_block_of_injective_sq_sub_mul'
  [CommRing R] [AddCommGroup W] [Module R W]
  (c : R) (hc : ∀ z : W, c • z = 0 → z = 0) (A B : Module.End R W)
  (hinj : Function.Injective (c ^ 2 • (1 : Module.End R W) - A * B)) :
-- imply
  Function.Injective (fun z : W × W => (c • z.1 + A z.2, B z.1 + c • z.2)) := by
-- proof
  let G : W × W →ₗ[R] W × W :=
    { toFun := fun z => (c • z.1 + A z.2, B z.1 + c • z.2)
      map_add' := fun z w => by
        simp only [Prod.fst_add, Prod.snd_add, smul_add, map_add, Prod.mk_add_mk]; abel_nf
      map_smul' := fun k z => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk, smul_add, smul_comm c k] }
  change Function.Injective G
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨z₀, z₁⟩ hz
  have h0 : c • z₀ + A z₁ = 0 := congrArg Prod.fst hz
  have h1 : B z₀ + c • z₁ = 0 := congrArg Prod.snd hz
  have hz₀ : (c ^ 2 • (1 : Module.End R W) - A * B) z₀ = 0 := by
    have e1 : c • z₁ = -(B z₀) := eq_neg_of_add_eq_zero_right h1
    have e2 : c • (c • z₀) = -(A (c • z₁)) := by rw [map_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_left h0]
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, pow_two, mul_smul, e2, e1,
      map_neg, neg_neg, sub_self]
  have hz₀' : z₀ = 0 := hinj (by rw [hz₀, map_zero])
  have hz₁ : z₁ = 0 := by
    rw [hz₀', map_zero, zero_add] at h1
    exact hc z₁ h1
  rw [hz₀', hz₁]
  rfl

private lemma injective_of_injective_baseChange
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  (K : Type*) [CommRing K] [Algebra R K] (hK : Function.Injective (algebraMap R K))
  (S : Module.End R M) (h : Function.Injective (S.baseChange K)) :
-- imply
  Function.Injective S := by
-- proof
  classical
  let b := Module.Free.chooseBasis R M
  have hincl : Function.Injective (fun z : M => (1 : K) ⊗ₜ[R] z) := by
    intro z w hzw
    apply b.repr.injective
    ext i
    have := congrArg (fun t => (b.baseChange K).repr t i) hzw
    simp only [Module.Basis.baseChange_repr_tmul] at this
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this
    exact hK this
  intro z w hzw
  apply hincl
  apply h
  simp only [LinearMap.baseChange_tmul, hzw]

/--
[DualAssembly_injective_gram_of_forall_joint_eigenvector_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DualAssembly_injective_gram_of_forall_joint_eigenvector_mul.lean)
-/
@[path]
private lemma main
  [AddCommGroup T] [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] T] [Module.Finite ℤ_[p] T] [Module.Free ℤ_[p] T] [Algebra ℤ_[p] K]
  {c : ℤ_[p]}
  {A B : Module.End ℤ_[p] T}
-- given
  (hK : Function.Injective (algebraMap ℤ_[p] K))
  (hc : c ≠ 0)
  (hAB : Commute A B)
  (h : ∀ (v : K ⊗[ℤ_[p]] T) (a b : K), v ≠ 0 → A.baseChange K v = a • v → B.baseChange K v = b • v → a * b ≠ (algebraMap ℤ_[p] K c) ^ 2) :
-- imply
  Function.Injective (fun z : T × T => (c • z.1 + A z.2, B z.1 + c • z.2)) := by
-- proof
  classical
  have hc' : ∀ z : T, c • z = 0 → z = 0 := by
    intro z hz
    let bb := Module.Free.chooseBasis ℤ_[p] T
    apply bb.repr.injective
    ext i
    have := congrArg (fun w => bb.repr w i) hz
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
    rw [map_zero, Finsupp.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left hc
  refine injective_block_of_injective_sq_sub_mul' c hc' A B ?_
  apply injective_of_injective_baseChange K hK
  have : FiniteDimensional K (K ⊗[ℤ_[p]] T) := Module.Finite.base_change ℤ_[p] K T
  have hcomm : Commute (A.baseChange K) (B.baseChange K) := by
    show A.baseChange K * B.baseChange K = B.baseChange K * A.baseChange K
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hAB.eq]
  have hS : (c ^ 2 • (1 : Module.End ℤ_[p] T) - A * B).baseChange K =
      (algebraMap ℤ_[p] K c) ^ 2 • (1 : Module.End K (K ⊗[ℤ_[p]] T)) - A.baseChange K * B.baseChange K := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.baseChange_mul,
      ← algebraMap_smul K (c ^ 2) (1 : Module.End K (K ⊗[ℤ_[p]] T)), map_pow]
  rw [hS]
  exact injective_sq_sub_mul_of_forall_joint_eigenvector (algebraMap ℤ_[p] K c) (A.baseChange K) (B.baseChange K) hcomm
    (fun v a b hv hA hB => h v a b hv hA hB)


-- created on 2026-10-24

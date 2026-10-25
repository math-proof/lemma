import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8


/--
[ueaIotaRange_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaIotaRange_fg
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤] :
-- imply
  (ueaIotaRange (R := R) (𝔤 := 𝔤)).FG := by
-- proof
  rw [ueaIotaRange, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

/--
[HomAdEquivariant.finite_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma HomAdEquivariant.finite_of_injection
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [IsNoetherianRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  {M N : LieBimodule R 𝔤}
  {ι : M.carrier →ₗ[R] N.carrier}
-- given
  (hι_inj : Function.Injective ι)
  (hι_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M.carrier), ι (M.leftAction u m) = N.leftAction u (ι m))
  (hι_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M.carrier), ι (M.rightAction u m) = N.rightAction u (ι m))
  (hN_fin : Module.Finite R (HomAdEquivariant V N)) :
-- imply
  Module.Finite R (HomAdEquivariant V M) := by
-- proof
  let pc := HomAdEquivariant.postcomp (R := R) (𝔤 := 𝔤) (V := V) ι hι_left hι_right
  have hpc_inj : Function.Injective pc := by
    intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
    simp only [pc, HomAdEquivariant.postcomp, LinearMap.coe_mk, AddHom.coe_mk] at heq
    apply Subtype.ext
    ext v
    have : ι (f₁ v) = ι (f₂ v) := by
      have := congr_arg (fun x => (x : V →ₗ[R] N.carrier) v) (Subtype.mk.inj heq)
      simpa [LinearMap.comp_apply] using this
    exact hι_inj this
  exact Module.Finite.of_injective pc hpc_inj

/--
[actionHom_image_in_HomFin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma actionHom_image_in_HomFin
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {act : MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) →ₐ[R] Module.End R M}
  {q : MaximalQuotient (evalHC Δ wg (wt + wg.ρ))}
-- given
  (_hVerma : IsVermaModule Δ M wt)
  (hcompat_act : ∀ (y : 𝔤) (m : M), act (MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) (UniversalEnvelopingAlgebra.ι R y)) m = ⁅y, m⁆) :
-- imply
  (act q : M →ₗ[R] M) ∈ @HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _ := by
-- proof
  let χ := evalHC Δ wg (wt + wg.ρ)
  let proj := MaximalQuotient.proj χ
  let actUEA := act.comp proj
  show IsFiniteTypeMap (𝔤 := 𝔤) M M (act q)
  suffices h : ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
    IsFiniteTypeMap (𝔤 := 𝔤) M M (actUEA u) by
    revert q; intro q
    exact Quot.inductionOn q (fun u => h u)
  intro u
  obtain ⟨S, hfin, hu_mem, hstab⟩ := ueaAdLocallyFinite (R := R) (𝔤 := 𝔤) u
  let imgS := S.map actUEA.toLinearMap
  refine ⟨imgS, ?_, ?_, ?_⟩
  ·
    exact Module.Finite.map S actUEA.toLinearMap
  ·
    exact Submodule.mem_map_of_mem hu_mem
  ·
    intro x f hf
    obtain ⟨v, hv_mem, hv_eq⟩ := Submodule.mem_map.mp hf
    subst hv_eq
    show adjointActionOnHom M M x (actUEA v) ∈ imgS
    have hcompat_uea : ∀ (y : 𝔤) (m : M),
      actUEA (UniversalEnvelopingAlgebra.ι R y) m = ⁅y, m⁆ := hcompat_act
    rw [ueaAction_adjoint_intertwine M actUEA hcompat_uea x v]
    exact Submodule.mem_map_of_mem (hstab x v hv_mem)

/--
[multMap_xi_eq_proj_comp_multMap_ug](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma multMap_xi_eq_proj_comp_multMap_ug
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {wt : Δ.𝔥 →ₗ[R] R}
  {x : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos)} :
-- imply
  multMap_xi Δ wg wt x = MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) (multMap_ug Δ x) := by
-- proof
  induction x using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul a b =>
    simp only [multMap_xi, multMap_ug, TensorProduct.lift.tmul, LinearMap.coe_mk,
      AddHom.coe_mk]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

/--
[weights_in_weightLattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma weights_in_weightLattice
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  [IsDomain R]
  [CharZero R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {chev : ChevalleyData Δ}
  {V : Type*}
  [AddCommGroup V]
  [Module R V]
  [Module.Finite R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [IsNoetherian R V]
  [Module.IsTorsionFree R V]
  {ν : Δ.𝔥 →ₗ[R] R}
-- given
  (hν : ν ∈ weights Δ V) :
-- imply
  chev.IsInWeightLattice ν := by
-- proof
  intro i
  have hν' : WeightSpace Δ V ν ≠ ⊥ := hν
  rw [Submodule.ne_bot_iff] at hν'
  obtain ⟨v, hv_mem, hv_ne⟩ := hν'
  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v := hv_mem
  have hh : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = ν (chev.simpleCoroot i) • v := hv_wt _
  by_cases hhz : (chev.simpleCoroot i : 𝔤) = 0
  · have hμv : ν (chev.simpleCoroot i) • v = 0 := by rw [← hh, hhz, zero_lie]
    have hμ0 : ν (chev.simpleCoroot i) = 0 := by
      by_contra hμ
      have hreg : IsRegular (ν (chev.simpleCoroot i)) :=
        ⟨fun a b hab => mul_left_cancel₀ hμ hab,
          fun a b hab => mul_right_cancel₀ hμ hab⟩
      have hsmul : IsSMulRegular V (ν (chev.simpleCoroot i)) :=
        Module.IsTorsionFree.isSMulRegular (M := V) hreg
      exact hv_ne (hsmul (show ν (chev.simpleCoroot i) • v = ν (chev.simpleCoroot i) • 0 by
        simp [hμv]))
    exact ⟨0, by simp [hμ0]⟩
  ·
    have t : IsSl2Triple (chev.simpleCoroot i : 𝔤) (chev.posGen i) (chev.negGen i) :=
      IsSl2Triple.mk hhz
        (chev.bracket_ef i)
        (by rw [two_nsmul]; exact chev.bracket_he i)
        (by rw [two_nsmul]; exact chev.bracket_hf i)
    set μ := ν (chev.simpleCoroot i)
    set e_i := chev.posGen i
    set h_i := (chev.simpleCoroot i : 𝔤)
    set ψ : ℕ → V := fun k => ((LieModule.toEnd R 𝔤 V e_i) ^ k) v
    have hψ_eig : ∀ k : ℕ, ⁅h_i, ψ k⁆ = (μ + 2 * (k : R)) • ψ k := by
      intro k
      induction k with
      | zero => simp [ψ, hh]
      | succ n ih =>
        simp only [ψ, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
        rw [leibniz_lie]
        rw [t.lie_h_e_smul R]
        simp only [ψ] at ih
        rw [ih]
        simp only [lie_smul, smul_lie]
        rw [← add_smul]
        congr 1
        push_cast
        ring
    have hψ_zero : ∃ k : ℕ, ψ k = 0 := by
      by_contra! hall
      have hs : (Set.range (fun (n : ℕ) => μ + 2 * (n : R))).Infinite := by
        rw [Set.infinite_range_iff]
        · infer_instance
        · intro a b hab
          simp only at hab
          exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := R)) (add_left_cancel hab)
      exact hs ((LieModule.toEnd R 𝔤 V h_i).eigenvectors_linearIndependent
        (Set.range (fun (n : ℕ) => μ + 2 * (n : R)))
        (fun ⟨_, hs⟩ => ψ (Classical.choose hs))
        (fun ⟨_, hs⟩ => by
          simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
          have hk := Classical.choose_spec hs
          simp only at hk
          refine ⟨?_, hall _⟩
          rw [LieModule.toEnd_apply_apply, hψ_eig, hk])).finite
    obtain ⟨k₀, hk₀_ne, hk₀_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
      (show ¬(ψ 0 = 0) from by simp [ψ, hv_ne]) hψ_zero
    have he_kill : ⁅e_i, ψ k₀⁆ = 0 := by
      show (LieModule.toEnd R 𝔤 V e_i) (((LieModule.toEnd R 𝔤 V e_i) ^ k₀) v) = 0
      rwa [← Module.End.mul_apply, ← pow_succ']
    have hprim : t.HasPrimitiveVectorWith (ψ k₀) (μ + 2 * (k₀ : R)) :=
      IsSl2Triple.HasPrimitiveVectorWith.mk hk₀_ne (hψ_eig k₀) he_kill
    obtain ⟨n, hn⟩ := hprim.exists_nat
    exact ⟨(n : ℤ) - 2 * (k₀ : ℤ), by push_cast; linear_combination hn⟩

/--
[UniversalEnvelopingAlgebra.induction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma induction_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {motive : UniversalEnvelopingAlgebra R 𝔤 → Prop}
  {u : UniversalEnvelopingAlgebra R 𝔤}
-- given
  (halg : ∀ r, motive (algebraMap R (UniversalEnvelopingAlgebra R 𝔤) r))
  (hι : ∀ x, motive (UniversalEnvelopingAlgebra.ι R x))
  (hmul : ∀ a b, motive a → motive b → motive (a * b))
  (hadd : ∀ a b, motive a → motive b → motive (a + b)) :
-- imply
  motive u := by
-- proof
  apply UniversalEnvelopingAlgebra.induction halg hι hmul hadd u

/--
[uea_ad_leibniz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma uea_ad_leibniz_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {x : 𝔤}
  {a b : UniversalEnvelopingAlgebra R 𝔤} :
-- imply
  UniversalEnvelopingAlgebra.ι R x * (a * b) - (a * b) * UniversalEnvelopingAlgebra.ι R x = (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b + a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
-- proof
  apply uea_ad_leibniz x a b

/--
[uea_ad_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma uea_ad_add_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {x : 𝔤}
  {v₁ v₂ : UniversalEnvelopingAlgebra R 𝔤} :
-- imply
  UniversalEnvelopingAlgebra.ι R x * (v₁ + v₂) - (v₁ + v₂) * UniversalEnvelopingAlgebra.ι R x = (UniversalEnvelopingAlgebra.ι R x * v₁ - v₁ * UniversalEnvelopingAlgebra.ι R x) + (UniversalEnvelopingAlgebra.ι R x * v₂ - v₂ * UniversalEnvelopingAlgebra.ι R x) := by
-- proof
  apply uea_ad_add x v₁ v₂

/--
[uea_comm_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma uea_comm_rel_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {x y : 𝔤} :
-- imply
  UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y - UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x = (UniversalEnvelopingAlgebra.ι R) ⁅x, y⁆ := by
-- proof
  apply uea_comm_rel x y

/--
[ueaScalarsSubmodule_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaScalarsSubmodule_fg_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤] :
-- imply
  (ueaScalarsSubmodule (R := R) (𝔤 := 𝔤)).FG := by
-- proof
  apply ueaScalarsSubmodule_fg

/--
[ueaAdLocallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaAdLocallyFinite_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {u : UniversalEnvelopingAlgebra R 𝔤} :
-- imply
  ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)), Module.Finite R S ∧ u ∈ S ∧ (∀ (x : 𝔤) (v : UniversalEnvelopingAlgebra R 𝔤), v ∈ S → (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) ∈ S) := by
-- proof
  apply ueaAdLocallyFinite u

/--
[ueaAction_adjoint_intertwine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaAction_adjoint_intertwine_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M}
  {x : 𝔤}
  {u : UniversalEnvelopingAlgebra R 𝔤}
-- given
  (hcompat : ∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
-- imply
  adjointActionOnHom M M x (act u) = act (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) := by
-- proof
  apply ueaAction_adjoint_intertwine M act hcompat x u

/--
[adjointActionOnHom_left_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma adjointActionOnHom_left_comp_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {x : 𝔤}
  {f : N →ₗ[R] N}
  {T : M →ₗ[R] N} :
-- imply
  adjointActionOnHom M N x (f.comp T) = (adjointActionOnHom N N x f).comp T + f.comp (adjointActionOnHom M N x T) := by
-- proof
  apply adjointActionOnHom_left_comp M N x f T

/--
[adjointActionOnHom_right_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma adjointActionOnHom_right_comp_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {x : 𝔤}
  {T : M →ₗ[R] N}
  {g : M →ₗ[R] M} :
-- imply
  adjointActionOnHom M N x (T.comp g) = (adjointActionOnHom M N x T).comp g + T.comp (adjointActionOnHom M M x g) := by
-- proof
  apply adjointActionOnHom_right_comp M N x T g

/--
[ueaAction_preserves_HomFin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaAction_preserves_HomFin_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {u : UniversalEnvelopingAlgebra R 𝔤}
  {T : M →ₗ[R] N}
-- given
  (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
-- imply
  (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈ HomFin (R := R) (𝔤 := 𝔤) M N ∧ T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈ HomFin (R := R) (𝔤 := 𝔤) M N := by
-- proof
  apply ueaAction_preserves_HomFin M N u T hT

/--
[leftAction_preserves_HomFin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma leftAction_preserves_HomFin_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {u : UniversalEnvelopingAlgebra R 𝔤}
  {T : M →ₗ[R] N}
-- given
  (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
-- imply
  (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈ HomFin (R := R) (𝔤 := 𝔤) M N := by
-- proof
  apply leftAction_preserves_HomFin M N u T hT

/--
[rightAction_preserves_HomFin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma rightAction_preserves_HomFin_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {u : UniversalEnvelopingAlgebra R 𝔤}
  {T : M →ₗ[R] N}
-- given
  (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
-- imply
  T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈ HomFin (R := R) (𝔤 := 𝔤) M N := by
-- proof
  apply rightAction_preserves_HomFin M N u T hT

/--
[homFinBimodule_adjointAction_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma homFinBimodule_adjointAction_val_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {x : 𝔤}
-- given
  (T : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) :
-- imply
  ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).adjointAction x T).val = adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x T.val := by
-- proof
  apply homFinBimodule_adjointAction_val M N x T

/--
[ueaActionFromLieModule_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma ueaActionFromLieModule_compat_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {x : 𝔤}
  {m : M} :
-- imply
  ueaActionFromLieModule M (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
-- proof
  apply ueaActionFromLieModule_compat M x m

/--
[isFiniteTypeMap_comp_mk_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DufloJoseph.lean)
-/
@[path]
private lemma isFiniteTypeMap_comp_mk_tensor_eq
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  [AddCommGroup N]
  [Module R N]
  [LieRingModule 𝔤 N]
  [LieModule R 𝔤 N]
  {V : Type*}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [Module.Finite R V]
  {v : V}
  {T : M →ₗ[R] N}
-- given
  (hT : IsFiniteTypeMap (𝔤 := 𝔤) M N T) :
-- imply
  IsFiniteTypeMap (𝔤 := 𝔤) M (TensorProduct R V N) ((TensorProduct.mk R V N v).comp T) := by
-- proof
  apply isFiniteTypeMap_comp_mk_tensor V v T hT


-- created on 2026-10-23
-- updated on 2026-10-24

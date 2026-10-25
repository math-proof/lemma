import Mathlib
import sympy.Basic
import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2


/--
[LinearMap.exists_factor_of_surjective_ker_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma LinearMap.exists_factor_of_surjective_ker_le
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R']
  [AddCommGroup A]
  [Module R' A]
  [AddCommGroup B]
  [Module R' B]
  [AddCommGroup C]
  [Module R' C]
  {p : A →ₗ[R'] B}
  {f : A →ₗ[R'] C}
-- given
  (hsurj : Function.Surjective p)
  (hker : LinearMap.ker p ≤ LinearMap.ker f) :
-- imply
  ∃ (ℓ : B →ₗ[R'] C), ∀ a, ℓ (p a) = f a := by
-- proof
  choose g hg using hsurj
  have well_def : ∀ (u₁ u₂ : A), p u₁ = p u₂ → f u₁ = f u₂ := by
    intro u₁ u₂ h
    have hmem : u₁ - u₂ ∈ LinearMap.ker p :=
      LinearMap.mem_ker.mpr (by rw [map_sub, h, sub_self])
    have := hker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
  exact ⟨{
    toFun := fun b => f (g b)
    map_add' := fun b₁ b₂ => by
      have h := well_def (g (b₁ + b₂)) (g b₁ + g b₂) (by rw [hg, map_add, hg, hg])
      rw [h, map_add]
    map_smul' := fun r b => by
      simp only [RingHom.id_apply]
      have h := well_def (g (r • b)) (r • g b) (by rw [hg, map_smul, hg])
      rw [h, map_smul]
  }, fun a => well_def (g (p a)) a (by rw [hg])⟩

/--
[pbw_ueaAct_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma pbw_ueaAct_surjective
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wt : Δ.𝔥 →ₗ[R] R}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M}
-- given
  (hM : IsHighestWeightModule Δ M wt)
  (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
-- imply
  Function.Surjective (fun u => ueaAct u hM.highestWeightVec) := by
-- proof
  intro m
  have hm_top : m ∈ (⊤ : LieSubmodule R 𝔤 M) := LieSubmodule.mem_top m
  rw [← hM.generates] at hm_top
  exact LieSubmodule.lieSpan_induction (R := R) (L := 𝔤)
    (p := fun x _ => ∃ a, (ueaAct a) hM.highestWeightVec = x)
    (fun x hx => by
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by simp [map_one, Module.End.one_apply]⟩)
    (⟨0, by simp [map_zero, LinearMap.zero_apply]⟩)
    (fun x y _ _ ⟨a, ha⟩ ⟨b, hb⟩ =>
      ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩)
    (fun r x _ ⟨a, ha⟩ =>
      ⟨r • a, by rw [map_smul, LinearMap.smul_apply, ha]⟩)
    (fun x y _ ⟨a, ha⟩ =>
      ⟨UniversalEnvelopingAlgebra.ι R x * a, by
        rw [map_mul, Module.End.mul_apply, ha, hcompat]⟩)
    hm_top

/--
[pbw_hc_map_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma pbw_hc_map_one
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤} :
-- imply
  HarishChandraMap Δ (1 : UniversalEnvelopingAlgebra R 𝔤) = (1 : UniversalEnvelopingAlgebra R Δ.𝔥) := by
-- proof
  show (betaMap Δ).comp (pbwTriangularIso Δ).symm.toLinearMap 1 = 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  have h1 : (pbwTriangularIso Δ).symm (1 : UniversalEnvelopingAlgebra R 𝔤) =
    (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) ⊗ₜ[R]
      ((1 : UniversalEnvelopingAlgebra R Δ.𝔥) ⊗ₜ[R]
        (1 : UniversalEnvelopingAlgebra R Δ.𝔫_pos)) := by
    apply (pbwTriangularIso Δ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (pbw_triangular_iso_one Δ).symm
  rw [h1]
  simp only [betaMap, TensorProduct.lift.tmul, LinearMap.flip_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, augmentation, map_one]
  simp only [LinearMap.lsmul_apply, one_smul]
  simp only [TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, map_one]
  simp only [LinearMap.lsmul_apply, one_smul]

/--
[center_acts_by_scalar_on_hwm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma center_acts_by_scalar_on_hwm
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {_wg : WeylGroupData Δ}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M}
  {z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)}
-- given
  (hM : IsHighestWeightModule Δ M wt)
  (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
-- imply
  ∃ (c : R), ∀ (m : M), ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m = c • m := by
-- proof
  have hz_comm : ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
    u * (z : UniversalEnvelopingAlgebra R 𝔤) = (z : UniversalEnvelopingAlgebra R 𝔤) * u := by
    intro u; exact (Subalgebra.mem_center_iff.mp z.prop) u
  have hact_comm : ∀ (x : 𝔤) (m : M),
    ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (ueaAct (UniversalEnvelopingAlgebra.ι R x) m) =
    ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m) := by
    intro x m
    have h1 : ueaAct ((z : UniversalEnvelopingAlgebra R 𝔤) * UniversalEnvelopingAlgebra.ι R x) m =
      ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (ueaAct (UniversalEnvelopingAlgebra.ι R x) m) := by
      have := map_mul ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (UniversalEnvelopingAlgebra.ι R x)
      rw [this]; rfl
    have h2 : ueaAct (UniversalEnvelopingAlgebra.ι R x * (z : UniversalEnvelopingAlgebra R 𝔤)) m =
      ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m) := by
      have := map_mul ueaAct (UniversalEnvelopingAlgebra.ι R x) (z : UniversalEnvelopingAlgebra R 𝔤)
      rw [this]; rfl
    rw [← h1, ← h2, hz_comm]
  have hlie_comm : ∀ (x : 𝔤) (m : M),
    ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) ⁅x, m⁆ =
    ⁅x, ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m⁆ := by
    intro x m
    rw [← hcompat x m, ← hcompat x (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m)]
    exact hact_comm x m
  have hzv_wt : ∀ (h : Δ.𝔥),
    ⁅(h : 𝔤), ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec⁆ =
    wt h • ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec := by
    intro h
    rw [← hlie_comm (h : 𝔤) hM.highestWeightVec, hM.cartan_action h, map_smul]
  obtain ⟨c, hc⟩ := IsHighestWeightModule.highestWeightSpace_one_dim hM _ hzv_wt
  refine ⟨c, ?_⟩
  set S : LieSubmodule R 𝔤 M := {
    toSubmodule := {
      carrier := {m : M | ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m = c • m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro r m hm
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [map_smul, hm, smul_comm]
    }
    lie_mem := by
      intro x m hm
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [hlie_comm x m, hm, lie_smul]
  }
  have hv_in_S : hM.highestWeightVec ∈ S := by
    show ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec = c • hM.highestWeightVec
    exact hc
  have hspan_le_S : LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} ≤ S :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_S)
  intro m
  exact (hM.generates ▸ hspan_le_S) (LieSubmodule.mem_top m)

/--
[evalWeight_algAction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma evalWeight_algAction_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {g : wg.W}
  {wt : Δ.𝔥 →ₗ[R] R}
  {p : UniversalEnvelopingAlgebra R Δ.𝔥} :
-- imply
  evalWeight Δ wt ((wg.algAction g) p) = evalWeight Δ (wg.dualAction g⁻¹ wt) p :=
-- proof
  wg.algDualCompat g wt p

/--
[WeylGroupData.dualAction_inv_cancel_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma WeylGroupData.dualAction_inv_cancel_left
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {g : wg.W}
  {wt : Δ.𝔥 →ₗ[R] R} :
-- imply
  wg.dualAction g⁻¹ (wg.dualAction g wt) = wt := by
-- proof
  rw [← wg.dualAction_mul g⁻¹ g wt, inv_mul_cancel, wg.dualAction_one]

/--
[schur_lie_module_scalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma schur_lie_module_scalar
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Field k]
  [IsAlgClosed k]
  [LieRing 𝔤']
  [LieAlgebra k 𝔤']
  [AddCommGroup M]
  [Module k M]
  [LieRingModule 𝔤' M]
  [LieModule k 𝔤' M]
  [Module.Finite k M]
  {T : Module.End k M}
-- given
  (hirr : LieModule.IsIrreducible k 𝔤' M)
  (hT : ∀ (x : 𝔤') (m : M), T ⁅x, m⁆ = ⁅x, T m⁆) :
-- imply
  ∃ c : k, ∀ m : M, T m = c • m := by
-- proof
  have hM : Nontrivial M := by
    have hne : (⊥ : LieSubmodule k 𝔤' M) ≠ ⊤ := IsSimpleOrder.bot_ne_top
    by_contra h; rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  set S : Module.End k M := T - c • (1 : Module.End k M) with hS_def
  have hS_comm : ∀ (x : 𝔤') (m : M), S ⁅x, m⁆ = ⁅x, S m⁆ := by
    intro x m
    simp only [hS_def, LinearMap.sub_apply, LinearMap.smul_apply]
    change T ⁅x, m⁆ - c • (⁅x, m⁆) = ⁅x, T m - c • m⁆
    rw [hT, lie_sub, lie_smul]
  let kerS : LieSubmodule k 𝔤' M :=
    { LinearMap.ker S with
      lie_mem := by
        intro x m hm
        show S ⁅x, m⁆ = 0
        rw [hS_comm x m]
        have : S m = 0 := hm
        rw [this, lie_zero] }
  have hker_ne_bot : kerS ≠ ⊥ := by
    intro h
    have hker_bot : (kerS : Submodule k M) = ⊥ :=
      (LieSubmodule.toSubmodule_eq_bot kerS).mpr h
    have : T.eigenspace c = ⊥ := by
      rwa [Module.End.eigenspace_def]
    exact (Module.End.hasEigenvalue_iff.mp hc) this
  have hker_top : kerS = ⊤ := by
    cases eq_bot_or_eq_top kerS with
    | inl h => exact absurd h hker_ne_bot
    | inr h => exact h
  have hker_sub_top : LinearMap.ker S = ⊤ :=
    (LieSubmodule.toSubmodule_eq_top kerS).mpr hker_top
  have hS_zero : S = 0 := LinearMap.ker_eq_top.mp hker_sub_top
  use c
  intro m
  have hSm : S m = 0 := by simp [hS_zero]
  change T m - c • m = 0 at hSm
  exact sub_eq_zero.mp hSm
set_option maxHeartbeats 800000 in

/--
[weyl_orbit_separation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma weyl_orbit_separation
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {mu nu : Δ.𝔥 →ₗ[R] R}
-- given
  (h : ∀ p : wg.invariantSubalgebra, evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) = evalWeight Δ nu (p : UniversalEnvelopingAlgebra R Δ.𝔥)) :
-- imply
  ∃ w : wg.W, nu = wg.dualAction w mu := by
-- proof
  apply wg.orbitSeparation mu nu
  intro p hp
  exact h ⟨p, hp⟩

/--
[evalWeight_weyl_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma evalWeight_weyl_invariant
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {w : wg.W}
  {mu : Δ.𝔥 →ₗ[R] R}
  {p : wg.invariantSubalgebra} :
-- imply
  evalWeight Δ (wg.dualAction w mu) (p : UniversalEnvelopingAlgebra R Δ.𝔥) = evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) := by
-- proof
  have key := evalWeight_algAction_eq Δ wg w⁻¹ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥)
  rw [p.prop w⁻¹] at key
  rwa [inv_inv] at key

/--
[cartan_isLieAbelian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraIsomorphism.lean)
-/
@[path]
private lemma cartan_isLieAbelian_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤} :
-- imply
  IsLieAbelian Δ.𝔥 := by
-- proof
  apply cartan_isLieAbelian R 𝔤 Δ


-- created on 2026-10-23
-- updated on 2026-10-24

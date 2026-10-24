import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.VermaModules
open TriangularDecomposition


namespace TriangularDecomposition

/--
[weightSubspace_eq_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma weightSubspace_eq_mathlib
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {μ : Δ.𝔥 →ₗ[R] R} :
-- imply
  Δ.weightSubspace M μ = (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
-- proof
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

end TriangularDecomposition

/--
[ueaSubalg_mul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_mul_apply
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M (u₁ * u₂)) m = (ueaSubalgAction Δ.𝔫_neg M u₁) ((ueaSubalgAction Δ.𝔫_neg M u₂) m) := by
-- proof
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ * u₂)) m = _
  rw [map_mul]; rfl

/--
[ueaSubalg_add_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_add_apply
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M (u₁ + u₂)) m = (ueaSubalgAction Δ.𝔫_neg M u₁) m + (ueaSubalgAction Δ.𝔫_neg M u₂) m := by
-- proof
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ + u₂)) m = _
  rw [map_add]; rfl

/--
[ueaSubalg_smul_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_smul_apply
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {r : R}
  {u₀ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M (r • u₀)) m = r • ((ueaSubalgAction Δ.𝔫_neg M u₀) m) := by
-- proof
  have : ueaSubalgAction Δ.𝔫_neg M (r • u₀) = r • ueaSubalgAction Δ.𝔫_neg M u₀ :=
    map_smul (ueaSubalgAction Δ.𝔫_neg M) r u₀
  rw [this]; rfl

/--
[ueaSubalg_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_one_apply
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
-- proof
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom 1) m = m
  rw [map_one]; rfl

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] {Δ : TriangularDecomposition R 𝔤} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
/--
[ueaSubalg_ι_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_ι_apply (n : ↥Δ.𝔫_neg) (m : M) :
  (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆ := by
  change ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥Δ.𝔫_neg) M))
    (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieModule.toEnd_apply_apply]; rfl

/--
[ueaSubalg_algebraMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg_algebraMap_apply
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {r : R}
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r)) m = r • m := by
-- proof
  have : ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r) = algebraMap R _ r :=
    AlgHom.commutes (ueaSubalgAction Δ.𝔫_neg M) r
  rw [this, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]; rfl
set_option maxHeartbeats 3200000 in

/--
[nminus_orbit_lie_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma nminus_orbit_lie_stable
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {x : 𝔤}
  {m : M}
-- given
  (hM : IsVermaModule Δ M wt)
  (hm : ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg, (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m) :
-- imply
  ∃ u' : UniversalEnvelopingAlgebra R Δ.𝔫_neg, (ueaSubalgAction Δ.𝔫_neg M u') hM.highestWeightVec = ⁅x, m⁆ := by
-- proof
  obtain ⟨u, hu⟩ := hm
  subst hu
  let Φ := ueaSubalgAction Δ.𝔫_neg M
  let vhw := hM.highestWeightVec
  suffices Q : ∀ (t : TensorAlgebra R ↥Δ.𝔫_neg) (y : 𝔤) (s : M),
    (∃ u₀, (Φ u₀) vhw = s) →
    (∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s⁆) →
    ∃ u₀, (Φ u₀) vhw =
      ⁅y, (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) t)) s⁆ by
    have hvhw : ∃ u₀, (Φ u₀) vhw = vhw := ⟨1, ueaSubalg_one_apply vhw⟩
    have base : ∀ (y : 𝔤), ∃ u₀, (Φ u₀) vhw = ⁅y, vhw⁆ := by
      intro y
      obtain ⟨n_neg, h, n_pos, hdecomp⟩ := Δ.decomp_exists y
      rw [hdecomp, add_lie, add_lie, hM.npos_action n_pos, hM.cartan_action h]
      simp only [add_zero]
      exact ⟨UniversalEnvelopingAlgebra.ι R n_neg + algebraMap R _ (wt h),
        by rw [ueaSubalg_add_apply, ueaSubalg_ι_apply, ueaSubalg_algebraMap_apply]⟩
    obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
      (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) u
    exact Q t x vhw hvhw base
  intro t
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro y s hs hstable
    have heq : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
      (algebraMap R _ r))) s = r • s := by
      have : RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ r
      rw [this]; exact ueaSubalg_algebraMap_apply r s
    rw [heq, lie_smul]
    obtain ⟨u', hu'⟩ := hstable y
    exact ⟨r • u', by rw [ueaSubalg_smul_apply, hu']⟩
  | ι n =>
    intro y s hs hstable
    have hι : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
      (TensorAlgebra.ι R n))) s = ⁅(n : 𝔤), s⁆ :=
      ueaSubalg_ι_apply n s
    rw [hι, leibniz_lie]
    obtain ⟨u₁, hu₁⟩ := hstable ⁅y, (n : 𝔤)⁆
    obtain ⟨u₂, hu₂⟩ := hstable y
    exact ⟨u₁ + UniversalEnvelopingAlgebra.ι R n * u₂,
      by rw [ueaSubalg_add_apply, ueaSubalg_mul_apply, ueaSubalg_ι_apply, hu₁, hu₂]⟩
  | add a b iha ihb =>
    intro y s hs hstable
    have hadd : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
      (a + b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a)) s +
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_add]; exact ueaSubalg_add_apply _ _ s
    rw [hadd, lie_add]
    obtain ⟨u₁, hu₁⟩ := iha y s hs hstable
    obtain ⟨u₂, hu₂⟩ := ihb y s hs hstable
    exact ⟨u₁ + u₂, by rw [ueaSubalg_add_apply, hu₁, hu₂]⟩
  | mul a b iha ihb =>
    intro y s hs hstable
    have hmul : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
      (a * b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a))
        ((Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s) := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_mul]; exact ueaSubalg_mul_apply _ _ s
    rw [hmul]
    set s' := (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s
    have hs' : ∃ u₀, (Φ u₀) vhw = s' := by
      obtain ⟨u_s, hu_s⟩ := hs
      let mkb : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg :=
        RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b
      exact ⟨mkb * u_s, by rw [ueaSubalg_mul_apply, hu_s]⟩
    have hstable' : ∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s'⁆ :=
      fun z => ihb z s hs hstable
    exact iha y s' hs' hstable'

/--
[pbw_verma_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma pbw_verma_surjective
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
-- given
  (hM : IsVermaModule Δ M wt) :
-- imply
  letI := instModuleUEASubalg Δ.𝔫_neg M Function.Surjective (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M hM.highestWeightVec) := by
-- proof
  letI := instModuleUEASubalg Δ.𝔫_neg M
  intro m
  set S : Set M := {m : M | ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
    (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m} with hS_def
  have hS_add : ∀ a b : M, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
    exact ⟨u₁ + u₂, by simp [map_add, LinearMap.add_apply]⟩
  have hS_zero : (0 : M) ∈ S := ⟨0, by simp [map_zero, LinearMap.zero_apply]⟩
  have hS_smul : ∀ (r : R) (a : M), a ∈ S → r • a ∈ S := by
    rintro r _ ⟨u, rfl⟩
    exact ⟨r • u, by simp [map_smul, LinearMap.smul_apply]⟩
  have hS_lie : ∀ (x : 𝔤) (a : M), a ∈ S → ⁅x, a⁆ ∈ S :=
    fun x a ha => nminus_orbit_lie_stable hM x a ha
  set N : LieSubmodule R 𝔤 M := {
    carrier := S
    add_mem' := fun ha hb => hS_add _ _ ha hb
    zero_mem' := hS_zero
    smul_mem' := fun r _ hx => hS_smul r _ hx
    lie_mem := fun {x a} ha => hS_lie x a ha
  } with hN_def
  have hvlam : hM.highestWeightVec ∈ N :=
    ⟨1, by simp [map_one]⟩
  have htop : N = ⊤ := by
    rw [eq_top_iff, ← hM.generates]
    exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hvlam)
  have hm : m ∈ N := htop ▸ trivial
  obtain ⟨u, hu⟩ : m ∈ S := hm
  exact ⟨u, hu⟩
section VermaProperties
variable {Δ : TriangularDecomposition R 𝔤}
variable {M : Type u_mod} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable {wt : Δ.𝔥 →ₗ[R] R}

/--
[IsVermaModule.hwv_not_mem_proper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma IsVermaModule.hwv_not_mem_proper
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {N : LieSubmodule R 𝔤 M}
-- given
  (hM : IsVermaModule Δ M wt)
  (hN : N ≠ ⊤) :
-- imply
  hM.highestWeightVec ∉ N := by
-- proof
  intro hmem
  apply hN
  rw [eq_top_iff]
  calc ⊤ = LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} := hM.generates.symm
    _ ≤ N := LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hmem)

/--
[weightSpace_eq_mathlib_weightSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma weightSpace_eq_mathlib_weightSpace
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {μ : Δ.𝔥 →ₗ[R] R} :
-- imply
  WeightSpace Δ M μ = (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
-- proof
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

/--
[weightSpace_eq_weightSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma weightSpace_eq_weightSubspace
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {μ : Δ.𝔥 →ₗ[R] R} :
-- imply
  WeightSpace Δ M μ = Δ.weightSubspace M μ := by
-- proof
  ext m; exact Iff.rfl

/--
[nminus_QPlus_weight_vector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma nminus_QPlus_weight_vector
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {rd : PositiveRootData Δ}
  {v : M}
  {β : Δ.𝔥 →ₗ[R] R}
-- given
  (hv : v ∈ WeightSpace Δ M wt)
  (hβ : rd.IsInQPlus β) :
-- imply
  ∃ (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg), u ≠ 0 ∧ (ueaSubalgAction Δ.𝔫_neg M u) v ∈ WeightSpace Δ M (wt - β) := by
-- proof
  obtain ⟨c, hc⟩ := hβ
  have single_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      ⁅(↑(rd.negRootVec α hα) : 𝔤), m⁆ ∈ WeightSpace Δ M (μ - α) := by
    intro α hα μ m hm h
    rw [leibniz_lie, rd.negRootVec_weight α hα h, hm h]
    rw [neg_smul, neg_lie, lie_smul]
    simp [LinearMap.sub_apply, sub_smul]
    abel
  have ι_act : ∀ (x : ↥(Δ.𝔫_neg)) (m : M), (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R x)) m = ⁅(x : 𝔤), m⁆ := by
    intro x m
    simp [ueaSubalgAction]
  have mul_act : ∀ (a b : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)) (m : M),
      (ueaSubalgAction Δ.𝔫_neg M (a * b)) m = (ueaSubalgAction Δ.𝔫_neg M a) ((ueaSubalgAction Δ.𝔫_neg M b) m) := by
    intro a b m
    show (ueaSubalgAction Δ.𝔫_neg M (a * b)) m = _
    rw [map_mul]
    rfl
  have one_act : ∀ (m : M), (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
    intro m; show (ueaSubalgAction Δ.𝔫_neg M 1) m = m; rw [map_one]; rfl
  have pow_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) (n : ℕ) (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      (ueaSubalgAction Δ.𝔫_neg M ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m ∈ WeightSpace Δ M (μ - n • α) := by
    intro α hα n
    induction n with
    | zero => intro μ m hm; simp; simpa using hm
    | succ n ih =>
      intro μ m hm
      rw [pow_succ', mul_act]
      have hrw : μ - (n + 1) • α = (μ - n • α) - α := by
        simp [add_smul, sub_sub]
      rw [hrw]
      have hmid := ih μ m hm
      have : (ueaSubalgAction Δ.𝔫_neg M
        (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)))
        ((ueaSubalgAction Δ.𝔫_neg M
          ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m) =
        ⁅(↑(rd.negRootVec α hα) : 𝔤),
          (ueaSubalgAction Δ.𝔫_neg M
            ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m⁆ := ι_act _ _
      rw [this]
      exact single_shift α hα (μ - n • α) _ hmid
  haveI := rd.uea_nminus_noZeroDivisors
  haveI := rd.uea_nminus_nontrivial
  suffices key : ∀ (S : Finset (Δ.𝔥 →ₗ[R] R)), S ⊆ rd.posRoots →
      ∃ (u : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)), u ≠ 0 ∧
        (ueaSubalgAction Δ.𝔫_neg M u) v ∈ WeightSpace Δ M (wt - ∑ α ∈ S, (c α) • α) by
    rw [hc]
    exact key rd.posRoots (Finset.Subset.refl _)
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_ne_zero, by rw [one_act]; simpa using hv⟩
  | @insert α₀ S₀ hα₀_notin ih =>
    intro hS
    have hS₀ : S₀ ⊆ rd.posRoots :=
      (Finset.subset_insert α₀ S₀).trans hS
    obtain ⟨u₀, hu₀_ne, hu₀_wt⟩ := ih hS₀
    have hα₀_mem : α₀ ∈ rd.posRoots := hS (Finset.mem_insert_self α₀ S₀)
    set u₁ := (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀
    refine ⟨u₁, ?_, ?_⟩
    ·
      exact mul_ne_zero (pow_ne_zero _ (rd.ι_negRootVec_ne_zero α₀ hα₀_mem)) hu₀_ne
    ·
      rw [Finset.sum_insert hα₀_notin]
      show (ueaSubalgAction Δ.𝔫_neg M u₁) v ∈ _
      change (ueaSubalgAction Δ.𝔫_neg M
        ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀)) v ∈ _
      rw [mul_act]
      have hrw : wt - (c α₀ • α₀ + ∑ α ∈ S₀, c α • α) =
        (wt - ∑ α ∈ S₀, c α • α) - c α₀ • α₀ := by
        simp [sub_sub, add_comm]
      rw [hrw]
      exact pow_shift α₀ hα₀_mem (c α₀) _ _ hu₀_wt

/--
[IsVermaModule.highest_weight_module_is_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma IsVermaModule.highest_weight_module_is_quotient
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
-- given
  (hM : IsVermaModule Δ M wt)
  (hV : IsHighestWeightModule Δ V wt) :
-- imply
  ∃ (η : M →ₗ⁅R, 𝔤⁆ V), Function.Surjective η := by
-- proof
  obtain ⟨η, hη⟩ := hM.universal_map V hV.highestWeightVec hV.cartan_action hV.npos_action
  refine ⟨η, ?_⟩
  rw [← LieModuleHom.range_eq_top]
  have hv_in_range : hV.highestWeightVec ∈ η.range := ⟨hM.highestWeightVec, hη⟩
  have hsub : LieSubmodule.lieSpan R 𝔤 {hV.highestWeightVec} ≤ η.range :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
  rw [hV.generates] at hsub
  exact top_le_iff.mp hsub

/--
[IsVermaModule.simpleQuotient_of_hwm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma IsVermaModule.simpleQuotient_of_hwm
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {J : LieSubmodule R 𝔤 M}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
-- given
  (hM : IsVermaModule Δ M wt)
  (_hJ_ne_top : J ≠ ⊤)
  (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J)
  (hV : IsHighestWeightModule Δ V wt) :
-- imply
  ∃ (π : V →ₗ⁅R, 𝔤⁆ (M ⧸ J)), Function.Surjective π := by
-- proof
  obtain ⟨η, hη_surj⟩ := hM.highest_weight_module_is_quotient V hV
  have hker_ne_top : η.ker ≠ ⊤ := by
    intro h
    have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
    have hV_zero : ∀ v : V, v = 0 := fun v => by
      obtain ⟨m, rfl⟩ := hη_surj v; exact hzero m
    exact hV.hwv_ne_zero (hV_zero hV.highestWeightVec)
  have hker_le_J : η.ker ≤ J := hJ_max η.ker hker_ne_top
  have hker_sub : η.toLinearMap.ker ≤ (LieSubmodule.Quotient.mk' J).toLinearMap.ker := by
    intro m hm
    rw [LinearMap.mem_ker, LieModuleHom.coe_toLinearMap]
    exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hker_le_J hm)
  let f_lin : V →ₗ[R] (M ⧸ J) :=
    (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub).comp
      (η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm.toLinearMap
  have hf : ∀ m : M, f_lin (η m) = LieSubmodule.Quotient.mk' J m := fun m => by
    show (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η m)) = _
    change (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η.toLinearMap m)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl
  refine ⟨⟨f_lin, ?_⟩, ?_⟩
  ·
    intro x v; obtain ⟨m, rfl⟩ := hη_surj v
    change f_lin (⁅x, η m⁆) = ⁅x, f_lin (η m)⁆
    rw [← η.map_lie, hf, hf, (LieSubmodule.Quotient.mk' J).map_lie]
  ·
    intro q
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J q
    exact ⟨η m, hf m⟩

/--
[IsVermaModule.le_maxProperSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma IsVermaModule.le_maxProperSubmodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {N : LieSubmodule R 𝔤 M}
-- given
  (hM : IsVermaModule Δ M wt)
  (hN : N ≠ ⊤) :
-- imply
  N ≤ hM.maxProperSubmodule :=
-- proof
  le_sSup hN

/--
[ker_ne_top_of_surj_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ker_ne_top_of_surj_irreducible
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M₀]
  [Module R M₀]
  [LieRingModule 𝔤 M₀]
  [LieModule R 𝔤 M₀]
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  {η : M₀ →ₗ⁅R,𝔤⁆ V}
-- given
  (hη : Function.Surjective η)
  (hirr : LieModule.IsIrreducible R 𝔤 V) :
-- imply
  η.ker ≠ ⊤ := by
-- proof
  intro h
  have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
  have hV : ∀ v : V, v = 0 := fun v => by obtain ⟨m, rfl⟩ := hη v; exact hzero m
  exact absurd (show (⊥ : LieSubmodule R 𝔤 V) = ⊤ by ext v; simp [hV v]) IsSimpleOrder.bot_ne_top

/--
[ker_eq_unique_max_of_surj_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ker_eq_unique_max_of_surj_irreducible
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M₀ : Type u_mod}
  [AddCommGroup M₀]
  [Module R M₀]
  [LieRingModule 𝔤 M₀]
  [LieModule R 𝔤 M₀]
  {wt : Δ.𝔥 →ₗ[R] R}
  {V : Type u_mod}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  {η : M₀ →ₗ⁅R,𝔤⁆ V}
  {J : LieSubmodule R 𝔤 M₀}
-- given
  (_hM : IsVermaModule Δ M₀ wt)
  (hη : Function.Surjective η)
  (hirr : LieModule.IsIrreducible R 𝔤 V)
  (hJ_ne_top : J ≠ ⊤)
  (hJ_max : ∀ (N : LieSubmodule R 𝔤 M₀), N ≠ ⊤ → N ≤ J) :
-- imply
  η.ker = J := by
-- proof
  apply le_antisymm
  ·
    exact hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr)
  ·
    obtain hbot | htop := IsSimpleOrder.eq_bot_or_eq_top (LieSubmodule.map η J)
    ·
      intro j hj
      have : η j ∈ LieSubmodule.map η J :=
        (LieSubmodule.mem_map (η j)).mpr ⟨j, hj, rfl⟩
      rw [hbot] at this; exact this
    ·
      exfalso; apply hJ_ne_top; rw [eq_top_iff]; intro m _
      have : η m ∈ LieSubmodule.map η J := htop ▸ trivial
      obtain ⟨j, hj, hjm⟩ := (LieSubmodule.mem_map (η m)).mp this
      have hmj : m - j ∈ η.ker := show η (m - j) = 0 by simp [hjm]
      have : m - j ∈ J :=
        hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr) hmj
      have := J.add_mem this hj; rwa [sub_add_cancel] at this
end

/--
[ueaSubalg_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma ueaSubalg__eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [CommRing R]
  {n : ↥Δ.𝔫_neg}
  {m : M} :
-- imply
  (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆ := by
-- proof
  apply ueaSubalg_ R 𝔤 n m

/--
[IsVermaModule.quotient_by_maximal_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma quotient_by_maximal_irreducible_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u_mod}
  [AddCommGroup M]
  [Module R M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {J : LieSubmodule R 𝔤 M}
-- given
  (_hM : IsVermaModule Δ M wt)
  (hJ_ne_top : J ≠ ⊤)
  (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) :
-- imply
  LieModule.IsIrreducible R 𝔤 (M ⧸ J) := by
-- proof
  apply IsVermaModule.quotient_by_maximal_irreducible R 𝔤 _hM J hJ_ne_top hJ_max

/--
[liftQ_comp_quotKerEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean)
-/
@[path]
private lemma liftQ_comp_quotKerEquiv_symm_apply_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [AddCommGroup M₀]
  [Module R M₀]
  [AddCommGroup N₁]
  [Module R N₁]
  [AddCommGroup N₂]
  [Module R N₂]
  {f₁ : M₀ →ₗ[R] N₁}
  {f₂ : M₀ →ₗ[R] N₂}
  {m : M₀}
-- given
  (hf₁ : Function.Surjective f₁)
  (h : f₁.ker ≤ f₂.ker) :
-- imply
  (f₁.ker.liftQ f₂ h) ((f₁.quotKerEquivOfSurjective hf₁).symm (f₁ m)) = f₂ m := by
-- proof
  apply liftQ_comp_quotKerEquiv_symm_apply R 𝔤 f₁ hf₁ f₂ h m


-- created on 2026-10-23
-- updated on 2026-10-24

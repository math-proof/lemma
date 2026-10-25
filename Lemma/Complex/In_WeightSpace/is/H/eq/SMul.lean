import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.KTypeDecomposition.Part3
open Module SL2GKModule


/--
[mem_weightSpace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma mem_weightSpace_iff
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V) :
-- imply
  v ∈ M.weightSpace n ↔ (Bracket.bracket M.H v) = (n : ℂ) • v := by
-- proof
  simp [weightSpace, hEnd]

/--
[H_acts_as_scalar_on_weight_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma H_acts_as_scalar_on_weight_space
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V)
-- given
  (hv : v ∈ weightSpace M n) :
-- imply
  (Bracket.bracket M.H v) = (n : ℂ) • v :=
-- proof
  (mem_weightSpace_iff M n v).mp hv

/--
[E_shifts_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma E_shifts_weight
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V)
-- given
  (hv : v ∈ M.weightSpace n) :
-- imply
  (Bracket.bracket M.E v) ∈ M.weightSpace (n + 2) := by
-- proof
  rw [mem_weightSpace_iff] at hv ⊢
  rw [leibniz_lie]
  rw [M.bracket_HE, zsmul_lie]
  rw [hv, lie_smul]
  rw [← Int.cast_smul_eq_zsmul ℂ (2 : ℤ) ((Bracket.bracket M.E v)), ← add_smul]
  congr 1
  push_cast
  ring

/--
[F_shifts_weight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma F_shifts_weight
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V)
-- given
  (hv : v ∈ weightSpace M n) :
-- imply
  (Bracket.bracket M.F v) ∈ weightSpace M (n - 2) := by
-- proof
  rw [mem_weightSpace_iff] at hv ⊢
  rw [leibniz_lie M.H M.F v, M.bracket_HF, hv, zsmul_lie, lie_smul]
  rw [← Int.cast_smul_eq_zsmul ℂ (-2 : ℤ) (Bracket.bracket M.F v)]
  rw [← add_smul]
  congr 1
  push_cast
  ring

/--
[iterLie_E_weight_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma iterLie_E_weight_shift
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V)
  (k : ℕ)
-- given
  (hv : v ∈ M.weightSpace n) :
-- imply
  iterLie M.E v k ∈ M.weightSpace (n + 2 * (k : ℤ)) := by
-- proof
  refine Nat.rec ?_ ?_ k
  ·
    simp
    exact hv
  ·
    intro k ih
    simp only [iterLie_succ]
    have hstep := E_shifts_weight M (n + 2 * (k : ℤ)) (iterLie M.E v k) ih
    convert hstep using 1
    congr 1
    omega

/--
[iterLie_F_weight_shift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma iterLie_F_weight_shift
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (n : ℤ)
  (v : V)
  (k : ℕ)
-- given
  (hv : v ∈ M.weightSpace n) :
-- imply
  iterLie M.F v k ∈ M.weightSpace (n - 2 * (k : ℤ)) := by
-- proof
  refine Nat.rec ?_ ?_ k
  ·
    simp
    exact hv
  ·
    intro k ih
    simp only [iterLie_succ]
    have hstep := F_shifts_weight M (n - 2 * (k : ℤ)) (iterLie M.F v k) ih
    convert hstep using 1
    congr 1
    omega

/--
[submodule_eq_of_le_sup_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma submodule_eq_of_le_sup_disjoint
  [AddCommGroup V]
  [Module ℂ V]
  {A B C : Submodule ℂ V}
-- given
  (hB_le_A : B ≤ A)
  (hBC_top : B ⊔ C = ⊤)
  (hAC_bot : A ⊓ C = ⊥) :
-- imply
  A = B := by
-- proof
  apply le_antisymm
  ·
    have h : A ⊓ C ⊔ B = A ⊓ (C ⊔ B) := inf_sup_assoc_of_le C hB_le_A
    have key : A ≤ A ⊓ C ⊔ B := by
      intro x hx
      have : x ∈ A ⊓ (C ⊔ B) :=
        ⟨hx, by
          rw [sup_comm]
          exact (hBC_top ▸ Submodule.mem_top)⟩
      rwa [← h] at this
    rwa [hAC_bot, bot_sup_eq] at key
  ·
    exact hB_le_A

/--
[eigenspace_inf_span_other_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma eigenspace_inf_span_other_eq_bot
  [AddCommGroup V]
  [Module ℂ V]
  {f : Module.End ℂ V}
  {μ : ℂ}
  {S : Set V}
-- given
  (hS : ∀ s ∈ S, ∃ m : ℂ, m ≠ μ ∧ s ∈ f.eigenspace m) :
-- imply
  f.eigenspace μ ⊓ Submodule.span ℂ S = ⊥ :=
-- proof
  (Disjoint.mono_right (Submodule.span_le.mpr fun s hs =>
    let ⟨m, hm_ne, hm_mem⟩ := hS s hs
    Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem hm_ne hm_mem))
    (Module.End.independent_genEigenspace f 1 μ)).eq_bot

/--
[sl2_generates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma sl2_generates
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (X : 𝔤) :
-- imply
  ∃ a b c : ℂ, X = a • M.H + b • M.E + c • M.F :=
-- proof
  M.sl2_span X

/--
[K_centralizes_H](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma K_centralizes_H
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (k : K) :
-- imply
  Ad k M.H = M.H :=
-- proof
  M.K_centralizes k

/--
[K_preserves_weightSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma K_preserves_weightSpace
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  (j : ℤ)
  (k : K)
  (v : V)
-- given
  (hv : v ∈ M.weightSpace j) :
-- imply
  M.toGKModule.σ k v ∈ M.weightSpace j := by
-- proof
  rw [mem_weightSpace_iff] at hv ⊢
  have heq := (M.toGKModule.equivariance k M.H v).symm
  rwa [K_centralizes_H M k, hv, map_smul] at heq

/--
[lie_action_preserves_parity_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma lie_action_preserves_parity_submodule
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  {n₀ : ℤ}
  (X : 𝔤)
  (v : V)
  (j : ℤ)
-- given
  (hv : v ∈ M.weightSpace j)
  (hparity : ∃ k : ℤ, j = n₀ + 2 * k) :
-- imply
  (Bracket.bracket X v) ∈ ⨆ (k : ℤ), M.weightSpace (n₀ + 2 * k) := by
-- proof
  obtain ⟨a, b, c, hX⟩ := sl2_generates M X
  rw [hX]
  simp only [add_lie, smul_lie]
  obtain ⟨kj, hkj⟩ := hparity
  have hHv : (Bracket.bracket M.H v) ∈ M.weightSpace j := by
    rw [H_acts_as_scalar_on_weight_space M j v hv]
    exact Submodule.smul_mem _ _ hv
  have hEv : (Bracket.bracket M.E v) ∈ M.weightSpace (j + 2) := E_shifts_weight M j v hv
  have hFv : (Bracket.bracket M.F v) ∈ M.weightSpace (j - 2) := F_shifts_weight M j v hv
  apply Submodule.add_mem _
  ·
    apply Submodule.add_mem _
    ·
      apply Submodule.mem_iSup_of_mem kj
      rw [hkj] at hHv
      exact Submodule.smul_mem _ a hHv
    ·
      apply Submodule.mem_iSup_of_mem (kj + 1)
      have : n₀ + 2 * (kj + 1) = j + 2 := by omega
      rw [this]
      exact Submodule.smul_mem _ b hEv
  ·
    apply Submodule.mem_iSup_of_mem (kj - 1)
    have : n₀ + 2 * (kj - 1) = j - 2 := by omega
    rw [this]
    exact Submodule.smul_mem _ c hFv

/--
[pbw_weight_same_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma pbw_weight_same_parity
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  (M : SL2GKModule 𝔤 K 𝔨 Ad V)
  {n m : ℤ}
-- given
  (hIrr : M.toGKModule.IsIrreducibleGKModule)
  (hn : n ∈ M.ktypeSet)
  (hm : m ∈ M.ktypeSet) :
-- imply
  Even n ↔ Even m := by
-- proof
  by_contra h_contra
  set S := ⨆ k : ℤ, M.weightSpace (n + 2 * k) with hS_def
  have hS_sub : M.toGKModule.IsSubmodule S := by
    constructor
    ·
      intro X w hw
      exact Submodule.iSup_induction (motive := fun w => (Bracket.bracket X w) ∈ S)
        _ hw
        (fun k v hv => lie_action_preserves_parity_submodule (n₀ := n) M X v (n + 2 * k) hv ⟨k, rfl⟩)
        (by simp [lie_zero])
        (fun a b ha hb => by show (Bracket.bracket X (a + b)) ∈ S; rw [lie_add]; exact Submodule.add_mem S ha hb)
    ·
      intro k w hw
      exact Submodule.iSup_induction (motive := fun w => M.toGKModule.σ k w ∈ S)
        _ hw
        (fun j v hv => Submodule.mem_iSup_of_mem j (K_preserves_weightSpace M (n + 2 * j) k v hv))
        (by simp [map_zero])
        (fun a b ha hb => by show M.toGKModule.σ k (a + b) ∈ S; rw [map_add]; exact Submodule.add_mem S ha hb)
  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot
    apply hn
    rw [eq_bot_iff]
    calc
      _ = M.weightSpace (n + 2 * 0) := by ring_nf
      _ ≤ S := le_iSup (fun k : ℤ => M.weightSpace (n + 2 * k)) 0
      _ = ⊥ := hbot
  have hS_top : S = ⊤ := by
    obtain hbot | htop := hIrr S hS_sub
    ·
      exact absurd hbot hS_ne_bot
    ·
      exact htop
  have hne : ∀ k : ℤ, (m : ℂ) ≠ (↑(n + 2 * k) : ℂ) := by
    intro k heq
    have hmk : m = n + 2 * k := by exact_mod_cast heq
    subst hmk
    exact h_contra (by simp [Int.even_add])
  have hdisjoint : Disjoint (M.weightSpace m) S := by
    have hind := Module.End.independent_genEigenspace M.hEnd (1 : WithTop ℕ)
    refine Disjoint.mono_right ?_ (hind (↑m))
    apply iSup_le
    intro k
    exact le_trans
      (le_iSup (fun _ : (↑(n + 2 * k) : ℂ) ≠ ↑m => M.hEnd.eigenspace ↑(n + 2 * k)) (hne k).symm)
      (le_iSup (fun μ : ℂ => ⨆ (_ : μ ≠ ↑m), M.hEnd.eigenspace μ) ↑(n + 2 * k))
  apply hm
  rw [disjoint_iff] at hdisjoint
  calc
    _ = M.weightSpace m ⊓ ⊤ := (inf_top_eq _).symm
    _ = M.weightSpace m ⊓ S := by rw [hS_top]
    _ = ⊥ := hdisjoint

/--
[iterLie_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma iterLie_zero_eq
  [LieRing 𝔤]
  [AddCommGroup V]
  [LieRingModule 𝔤 V]
  (X : 𝔤)
  (v : V) :
-- imply
  iterLie X v 0 = v := by
-- proof
  apply SL2GKModule.iterLie_zero X v

/--
[iterLie_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma iterLie_succ_eq
  [LieRing 𝔤]
  [AddCommGroup V]
  [LieRingModule 𝔤 V]
  (X : 𝔤)
  (v : V)
  (k : ℕ) :
-- imply
  iterLie X v (k + 1) = (Bracket.bracket X (iterLie X v k)) := by
-- proof
  apply SL2GKModule.iterLie_succ X v k

/--
[sl2_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KTypeDecomposition.lean)
-/
@[path]
private lemma sl2_linearIndependent_eq :
-- imply
  LinearIndependent ℂ ![sl2H, sl2E, sl2F] := by
-- proof
  apply sl2_linearIndependent


-- created on 2026-10-23
-- updated on 2026-10-24

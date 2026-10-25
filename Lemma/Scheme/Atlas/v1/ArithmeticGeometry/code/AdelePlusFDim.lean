import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.AdelePlusFDim
open FunctionFieldAdeleRing DiscreteValuationFamily
open scoped RestrictedProduct


/--
[AF_subspace_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma AF_subspace_mono
  [Field F]
  [DecidableEq P]
  {A B : P → ℤ}
-- given
  (hAB : ∀ p, A p ≤ B p) :
-- imply
  AF_subspace (F := F) (O := O) k A ≤ AF_subspace (F := F) (O := O) k B :=
-- proof
  sup_le_sup_right (adeleSpace_mono k hAB) _

/--
[rrSpaceAdele_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma rrSpaceAdele_mono
  [Field F]
  [DecidableEq P]
  {D D' : P → ℤ}
-- given
  (h : ∀ p, D p ≤ D' p) :
-- imply
  rrSpaceAdele (F := F) (O := O) k D ≤ rrSpaceAdele (F := F) (O := O) k D' := by
-- proof
  intro f hf
  simp only [rrSpaceAdele, Submodule.mem_comap] at hf ⊢
  exact adeleSpace_mono k h hf

/--
[rrSpaceAdele_fd_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma rrSpaceAdele_fd_step
  [Field F]
  [DecidableEq P]
  {D D' : P →₀ ℤ}
-- given
  (h : ∀ p, D p ≤ D' p)
  (hFD_D : FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (D : P → ℤ))) :
-- imply
  FiniteDimensional k (rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ)) := by
-- proof
  have h_adele := adeleSpace_quotient_finrank_eq (F := F) (O := O) k D D' h
  obtain ⟨hFD_adele, _⟩ := h_adele
  haveI := hFD_adele
  have h_mono : rrSpaceAdele (F := F) (O := O) k (D : P → ℤ) ≤
    rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ) :=
    rrSpaceAdele_mono k h
  set L' := rrSpaceAdele (F := F) (O := O) k (D' : P → ℤ)
  set L := rrSpaceAdele (F := F) (O := O) k (D : P → ℤ)
  set N := Submodule.comap L'.subtype L with hN_def
  haveI : FiniteDimensional k ↥N := by
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe h_mono).symm
  set A' := adeleSpace (F := F) (O := O) k (D' : P → ℤ)
  set A := adeleSpace (F := F) (O := O) k (D : P → ℤ)
  set M := Submodule.comap A'.subtype A with hM_def
  have h_diag_mem : ∀ (f : ↥L'), diagonalLinearMap (F := F) (P := P) (O := O) k f.val ∈ A' := by
    intro ⟨f, hf⟩
    exact hf
  let ι : ↥L' →ₗ[k] ↥A' := {
    toFun := fun f => ⟨diagonalLinearMap k f.val, h_diag_mem f⟩
    map_add' := fun a b => by ext; simp [map_add]
    map_smul' := fun c a => by ext; simp [map_smul]
  }
  have h_ι_N : ∀ (f : ↥L') (hf : f ∈ N), ι f ∈ M := by
    intro ⟨f, hf_L'⟩ hf_N
    simp only [N, Submodule.mem_comap, Submodule.subtype_apply] at hf_N
    simp only [ι, M, Submodule.mem_comap, Submodule.subtype_apply]
    exact hf_N
  let ι_bar : (↥L' ⧸ N) →ₗ[k] (↥A' ⧸ M) :=
    N.liftQ (M.mkQ.comp ι) (fun x hx => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h_ι_N x hx)
  have h_ι_inj : Function.Injective ι_bar := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [LinearMap.mem_ker] at hq
    simp only [ι_bar, Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply] at hq
    rw [Submodule.Quotient.mk_eq_zero] at hq ⊢
    simp only [M, Submodule.mem_comap, Submodule.subtype_apply] at hq
    simp only [N, Submodule.mem_comap, Submodule.subtype_apply]
    exact hq
  haveI : FiniteDimensional k (↥L' ⧸ N) :=
    Module.Finite.of_injective ι_bar h_ι_inj
  exact Module.Finite.of_submodule_quotient N

/--
[diagonalLinearMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma diagonalLinearMap_injective
  [Field F]
  [DecidableEq P]
  [Nonempty P] :
-- imply
  Function.Injective (diagonalLinearMap (F := F) (P := P) (O := O) k) := by
-- proof
  intro a b hab
  have h := FunctionFieldAdeleRing.ext_iff.mp hab
  exact h (Classical.arbitrary P)

/--
[rrSpaceAdele_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma rrSpaceAdele_map_eq
  [Field F]
  [DecidableEq P]
  {D : P → ℤ} :
-- imply
  Submodule.map (diagonalLinearMap (F := F) (P := P) (O := O) k) (rrSpaceAdele (F := F) (O := O) k D) = adeleSpace (F := F) (O := O) k D ⊓ principalAdeles (F := F) (P := P) (O := O) k := by
-- proof
  ext x
  simp only [Submodule.mem_map, rrSpaceAdele, Submodule.mem_comap, Submodule.mem_inf,
    principalAdeles, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨hf, ⟨f, rfl⟩⟩
  · rintro ⟨hx, f, rfl⟩
    exact ⟨f, hx, rfl⟩

/--
[finrank_sup_quotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma finrank_sup_quotient_eq
  [Field F]
  [DecidableEq P]
  [DivisionRing R]
  [AddCommGroup M]
  [Module R M]
  {A B F_sub : Submodule R M}
  [hFD : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype A)]
  [hFD_inf : FiniteDimensional R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub))]
-- given
  (hAB : A ≤ B) :
-- imply
  FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) ∧ Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) + Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) = Module.finrank R (↥B ⧸ Submodule.comap B.subtype A) := by
-- proof
  set T := A ⊔ (B ⊓ F_sub) with hT_def
  have hAT : A ≤ T := le_sup_left
  have hTB : T ≤ B := sup_le hAB inf_le_left
  have h_modular : B ⊓ (A ⊔ F_sub) = T := by
    rw [sup_comm (a := A) (b := F_sub)]
    rw [← inf_sup_assoc_of_le F_sub hAB]
    rw [sup_comm]
  have hBsup : B ⊔ (A ⊔ F_sub) = B ⊔ F_sub := by
    rw [← sup_assoc, sup_eq_left.mpr hAB]
  have hABF_inf : A ⊓ (B ⊓ F_sub) = A ⊓ F_sub := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]
  have e_2nd_BF := LinearMap.quotientInfEquivSupQuotient (B ⊓ F_sub) A
  have h_comap_eq_inf : Submodule.comap (B ⊓ F_sub).subtype (B ⊓ F_sub) ⊓
    Submodule.comap (B ⊓ F_sub).subtype A =
    Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub) := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hx.2⟩, fun ⟨h, _⟩ => h⟩
  have e_TA : (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) ≃ₗ[R]
    (↥((B ⊓ F_sub) ⊔ A) ⧸ Submodule.comap ((B ⊓ F_sub) ⊔ A).subtype A) := by
    rw [← h_comap_eq_inf]; exact e_2nd_BF
  have hTA_comm : (B ⊓ F_sub) ⊔ A = T := sup_comm (a := B ⊓ F_sub) (b := A)
  haveI : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype A) := by
    rw [← hTA_comm]
    exact Module.Finite.equiv e_TA
  have e_2nd_B := LinearMap.quotientInfEquivSupQuotient B (A ⊔ F_sub)
  have h_comap_eq_T : Submodule.comap B.subtype B ⊓ Submodule.comap B.subtype (A ⊔ F_sub) =
    Submodule.comap B.subtype T := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    rw [← h_modular]
    exact ⟨fun h => ⟨hx, h⟩, fun ⟨_, h⟩ => h⟩
  have e_BT : (↥B ⧸ Submodule.comap B.subtype T) ≃ₗ[R]
    (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) := by
    rw [← h_comap_eq_T, ← hBsup]; exact e_2nd_B
  haveI : FiniteDimensional R (↥B ⧸ Submodule.comap B.subtype T) := by
    have h_le : Submodule.comap B.subtype A ≤ Submodule.comap B.subtype T :=
      Submodule.comap_mono hAT
    let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[R]
      (↥B ⧸ Submodule.comap B.subtype T) :=
      (Submodule.comap B.subtype A).liftQ
        (Submodule.comap B.subtype T).mkQ
        (fun x hx => by
          simp only [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact h_le hx)
    have hf_surj : Function.Surjective f := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      refine ⟨Submodule.Quotient.mk y, ?_⟩
      simp only [f, Submodule.liftQ_apply, Submodule.mkQ_apply]
    exact Module.Finite.of_surjective f hf_surj
  haveI : FiniteDimensional R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    Module.Finite.equiv e_BT
  have h_chain := finrank_comap_chain A T B hAT hTB
  obtain ⟨_, h_chain_eq⟩ := h_chain
  have hd_BT : Module.finrank R (↥B ⧸ Submodule.comap B.subtype T) =
    Module.finrank R (↥(B ⊔ F_sub) ⧸ Submodule.comap (B ⊔ F_sub).subtype (A ⊔ F_sub)) :=
    LinearEquiv.finrank_eq e_BT
  have hd_TA : Module.finrank R (↥T ⧸ Submodule.comap T.subtype A) =
    Module.finrank R (↥(B ⊓ F_sub) ⧸ Submodule.comap (B ⊓ F_sub).subtype (A ⊓ F_sub)) := by
    rw [← hTA_comm]; exact (LinearEquiv.finrank_eq e_TA).symm
  exact ⟨inferInstance, by omega⟩

/--
[adeleDivisorDeg_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma adeleDivisorDeg_add
  [Field F]
  [DecidableEq P]
  {A B : P →₀ ℤ} :
-- imply
  adeleDivisorDeg (F := F) (k := k) (O := O) (A + B) = adeleDivisorDeg (F := F) (k := k) (O := O) A + adeleDivisorDeg (F := F) (k := k) (O := O) B := by
-- proof
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_add_index (fun p => by simp) (fun p _ a b => by ring)]

/--
[adeleDivisorDeg_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdelePlusFDim.lean)
-/
@[path]
lemma adeleDivisorDeg_sub
  [Field F]
  [DecidableEq P]
  {A B : P →₀ ℤ} :
-- imply
  adeleDivisorDeg (F := F) (k := k) (O := O) (B - A) = adeleDivisorDeg (F := F) (k := k) (O := O) B - adeleDivisorDeg (F := F) (k := k) (O := O) A := by
-- proof
  rw [sub_eq_add_neg, adeleDivisorDeg_add]
  congr 1
  simp only [adeleDivisorDeg]
  rw [Finsupp.sum_neg_index (fun p => by simp)]
  simp only [Finsupp.sum, neg_mul]
  exact Finset.sum_neg_distrib _


-- created on 2026-10-23

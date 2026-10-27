import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section18
open Topology BigOperators AlgebraicTopology CategoryTheory EulerCharacteristic


namespace EulerCharacteristic

/--
[abelianGroupRank_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_additive
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [Module.Finite ℤ A]
  [Module.Finite ℤ B]
  [Module.Finite ℤ C]
  {f : A →ₗ[ℤ] B}
  {g : B →ₗ[ℤ] C}
-- given
  (hf : Function.Injective f)
  (hg : Function.Surjective g)
  (hfg : LinearMap.range f = LinearMap.ker g) :
-- imply
  abelianGroupRank B = abelianGroupRank A + abelianGroupRank C := by
-- proof
  unfold abelianGroupRank
  let f' := LinearMap.baseChange ℚ f
  let g' := LinearMap.baseChange ℚ g
  have hf'_inj : Function.Injective f' :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have hg'_surj : Function.Surjective g' :=
    LinearMap.lTensor_surjective _ hg
  have hexact_fg : Function.Exact f g := by
    intro y
    constructor
    · intro hy
      have : y ∈ LinearMap.ker g := LinearMap.mem_ker.mpr hy
      rw [← hfg] at this
      exact LinearMap.mem_range.mp this
    · intro ⟨x, hx⟩
      have : y ∈ LinearMap.range f := ⟨x, hx⟩
      rw [hfg] at this
      exact LinearMap.mem_ker.mp this
  have hexact' : Function.Exact (LinearMap.lTensor ℚ f) (LinearMap.lTensor ℚ g) :=
    Module.Flat.lTensor_exact ℚ hexact_fg
  have hfg' : f'.range = g'.ker := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      rw [LinearMap.mem_ker]
      have := (hexact' (f' a)).mpr ⟨a, rfl⟩
      rwa [ha] at this
    · intro hx
      rw [LinearMap.mem_ker] at hx
      exact (hexact' x).mp hx
  have h1 : Module.finrank ℚ (TensorProduct ℤ ℚ B) =
    Module.finrank ℚ (LinearMap.ker g') + Module.finrank ℚ (LinearMap.range g') := by
    have := LinearMap.finrank_range_add_finrank_ker g'
    omega
  have h2 : Module.finrank ℚ (LinearMap.range g') = Module.finrank ℚ (TensorProduct ℤ ℚ C) := by
    have htop : LinearMap.range g' = ⊤ := LinearMap.range_eq_top.mpr hg'_surj
    rw [htop, finrank_top]
  have h3 : Module.finrank ℚ (LinearMap.ker g') = Module.finrank ℚ (TensorProduct ℤ ℚ A) := by
    rw [← hfg']
    exact (LinearEquiv.finrank_eq (LinearEquiv.ofInjective f' hf'_inj)).symm
  linarith

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_eq_of_addEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_eq_of_addEquiv
  [AddCommGroup A]
  [AddCommGroup B]
  {e : A ≃+ B} :
-- imply
  abelianGroupRank A = abelianGroupRank B := by
-- proof
  unfold abelianGroupRank
  exact (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ) e.toIntLinearEquiv).finrank_eq

end EulerCharacteristic

namespace EulerCharacteristic

/--
[singularHomologyRank_eq_of_homotopyEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma singularHomologyRank_eq_of_homotopyEquiv
  {X Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {e : ContinuousMap.HomotopyEquiv X Y}
  {k : ℕ} :
-- imply
  singularHomologyRank X k = singularHomologyRank Y k :=
-- proof
  abelianGroupRank_eq_of_addEquiv
    (ContractibleHomology.singularHomologyIsoOfHomotopyEquiv e k).addCommGroupIsoToAddEquiv

end EulerCharacteristic

namespace EulerCharacteristic

/--
[telescoping_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma telescoping_general
  {N : ℕ}
  {b : ℕ → ℤ} :
-- imply
  ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * b k + ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * b (k + 1) = b 0 - (-1 : ℤ) ^ N * b N := by
-- proof
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : (-1 : ℤ) ^ (n + 1) = -(-1 : ℤ) ^ n := by ring
    rw [h1]
    linarith [ih]

end EulerCharacteristic

namespace EulerCharacteristic

/--
[alternating_sum_chain_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma alternating_sum_chain_eq_homology
  {N : ℕ}
-- given
  (c h b : ℕ → ℤ)
  (hb0 : b 0 = 0)
  (hbN : b N = 0)
  (hdecomp : ∀ k, k < N → c k = h k + b k + b (k + 1)) :
-- imply
  ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * c k = ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * h k := by
-- proof
  have hrewrite : ∀ k ∈ Finset.range N, (-1 : ℤ) ^ k * c k =
    (-1 : ℤ) ^ k * h k + (-1 : ℤ) ^ k * b k + (-1 : ℤ) ^ k * b (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [hdecomp k hk]
    ring
  rw [Finset.sum_congr rfl hrewrite]
  simp only [Finset.sum_add_distrib]
  have htelescope := telescoping_general N b
  rw [hb0, hbN] at htelescope
  simp only [mul_zero, sub_zero] at htelescope
  linarith

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_freeAbelianGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_freeAbelianGroup
  {S : Type*}
  [Finite S] :
-- imply
  abelianGroupRank (FreeAbelianGroup S) = Nat.card S := by
-- proof
  classical
  haveI : Fintype S := Fintype.ofFinite S
  rw [show abelianGroupRank (FreeAbelianGroup S) =
    abelianGroupRank (S →₀ ℤ) from
    abelianGroupRank_eq_of_addEquiv (FreeAbelianGroup.equivFinsupp S)]
  unfold abelianGroupRank
  have : Module.finrank ℚ (TensorProduct ℤ ℚ (S →₀ ℤ)) =
    Module.finrank ℚ (S →₀ ℚ) :=
    (TensorProduct.finsuppScalarRight ℤ ℚ ℚ S).finrank_eq
  rw [this, Module.finrank_finsupp_self]
  exact (Nat.card_eq_fintype_card).symm

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_cellularHomology_eq_singularHomologyRank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_cellularHomology_eq_singularHomologyRank
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k : ℕ} :
-- imply
  abelianGroupRank (CWHomology.cellularHomologyGroup k X) = singularHomologyRank X k := by
-- proof
  unfold singularHomologyRank
  show abelianGroupRank ↑(CWHomology.cellularHomologyGroup k X) =
    abelianGroupRank ↑(AlgebraicTopologyI.SingularHomologyGroup k X)
  exact abelianGroupRank_eq_of_addEquiv
    (CWHomology.cellularHomologyGroup_iso_singularHomologyGroup k X).addCommGroupIsoToAddEquiv

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_ker_add_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_ker_add_range
  [AddCommGroup A]
  [AddCommGroup B]
  [Module.Finite ℤ A]
  [Module.Finite ℤ B]
  {f : A →ₗ[ℤ] B} :
-- imply
  abelianGroupRank A = abelianGroupRank (LinearMap.ker f) + abelianGroupRank (LinearMap.range f) :=
-- proof
  abelianGroupRank_additive
    (LinearMap.ker f).subtype
    f.rangeRestrict
    (Subtype.val_injective)
    (LinearMap.surjective_rangeRestrict f)
    (by rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict])

end EulerCharacteristic

namespace EulerCharacteristic

/--
[chain_complex_kernel_image_homology_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma chain_complex_kernel_image_homology_rank
  {C : ChainComplex AddCommGrpCat ℕ}
  {k : ℕ}
-- given
  (hC_fin : ∀ k, Module.Finite ℤ (C.X k)) :
-- imply
  abelianGroupRank (LinearMap.ker (chainDifferentialLinearMap C k)) = abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C (k + 1))) + abelianGroupRank (C.homology (k + 1)) := by
-- proof
  let S := C.sc' (k + 2) (k + 1) k
  have hprev : (ComplexShape.down ℕ).prev (k + 1) = k + 2 := ChainComplex.prev ℕ (k + 1)
  have hnext : (ComplexShape.down ℕ).next (k + 1) = k := ChainComplex.next_nat_succ k
  let compIso := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' (k + 2) (k + 1) k hprev hnext)) ≪≫ S.abHomologyIso
  have hHomRank : abelianGroupRank (C.homology (k + 1)) =
    abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) :=
    abelianGroupRank_eq_of_addEquiv compIso.addCommGroupIsoToAddEquiv
  haveI hfin1 : Module.Finite ℤ (C.X (k + 1)) := hC_fin (k + 1)
  haveI : Module.Finite ℤ (AddMonoidHom.ker S.g.hom) := by
    have : Module.Finite ℤ (LinearMap.ker (chainDifferentialLinearMap C k)) := inferInstance
    convert this using 1
  haveI hfin2 : Module.Finite ℤ (C.X (k + 2)) := hC_fin (k + 2)
  haveI : Module.Finite ℤ (↑S.X₁) := hfin2
  let tcLM := S.abToCycles.toIntLinearMap
  haveI : Module.Finite ℤ (LinearMap.range tcLM) := inferInstance
  haveI : Module.Finite ℤ (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    Module.Finite.quotient ℤ _
  have hKerSES : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
    abelianGroupRank (LinearMap.range tcLM) +
      abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    abelianGroupRank_additive (LinearMap.range tcLM).subtype (LinearMap.range tcLM).mkQ
      Subtype.val_injective (Submodule.Quotient.mk_surjective _)
      (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ _).symm)
  have hQuotEq : abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) =
    abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) := by
    congr 1
  have hKerEq : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
    abelianGroupRank (LinearMap.ker (chainDifferentialLinearMap C k)) := by
    congr 1
  have hRangeEq : abelianGroupRank (LinearMap.range tcLM) =
    abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C (k + 1))) := by
    apply abelianGroupRank_eq_of_addEquiv
    have hval : ∀ y : C.X (k + 2),
      (S.abToCycles y : AddMonoidHom.ker S.g.hom).1 =
      chainDifferentialLinearMap C (k + 1) y := by
      intro y; rfl
    refine {
      toFun := fun ⟨a, ha⟩ => ⟨a.1, by
        rw [LinearMap.mem_range] at ha ⊢; obtain ⟨y, hy⟩ := ha
        exact ⟨y, by rw [← hval]; exact congr_arg Subtype.val hy⟩⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, by
        rw [LinearMap.mem_range] at hx; obtain ⟨y, hy⟩ := hx
        rw [← hy, ← hval]; exact (S.abToCycles y).2⟩, by
        rw [LinearMap.mem_range] at hx ⊢; obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext (by show (S.abToCycles y).1 = x; rw [hval, hy])⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
    }
  linarith [hKerEq, hKerSES, hQuotEq, hHomRank, hRangeEq]

end EulerCharacteristic

namespace EulerCharacteristic

/--
[chain_complex_rank_decomposition_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma chain_complex_rank_decomposition_zero
  {C : ChainComplex AddCommGrpCat ℕ}
-- given
  (hC_fin : ∀ k, Module.Finite ℤ (C.X k)) :
-- imply
  abelianGroupRank (C.X 0) = abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C 0)) + abelianGroupRank (C.homology 0) := by
-- proof
  let S := C.sc' 1 0 0
  have hg_zero : S.g = 0 := C.shape 0 0 (by decide)
  have hker_top : AddMonoidHom.ker S.g.hom = ⊤ := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_top, iff_true]
    show S.g.hom x = 0
    rw [hg_zero]
    simp
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 := ChainComplex.prev ℕ 0
  have hnext : (ComplexShape.down ℕ).next 0 = 0 := ChainComplex.next_nat_zero
  let compIso := (CategoryTheory.ShortComplex.homologyMapIso
    (C.isoSc' 1 0 0 hprev hnext)) ≪≫ S.abHomologyIso
  have hHomRank : abelianGroupRank (C.homology 0) =
    abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) :=
    abelianGroupRank_eq_of_addEquiv compIso.addCommGroupIsoToAddEquiv
  let kerEquiv : AddMonoidHom.ker S.g.hom ≃+ (C.X 0) := {
    toFun := fun ⟨x, _⟩ => x
    invFun := fun x => ⟨x, by rw [hker_top]; trivial⟩
    left_inv := fun ⟨_, _⟩ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
  }
  haveI hfin0 : Module.Finite ℤ (C.X 0) := hC_fin 0
  haveI hfin1 : Module.Finite ℤ (C.X 1) := hC_fin 1
  haveI : Module.Finite ℤ (AddMonoidHom.ker S.g.hom) :=
    Module.Finite.equiv kerEquiv.symm.toIntLinearEquiv
  haveI : Module.Finite ℤ (↑S.X₁) := hfin1
  let tcLM := S.abToCycles.toIntLinearMap
  haveI : Module.Finite ℤ (LinearMap.range tcLM) := inferInstance
  haveI : Module.Finite ℤ (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    Module.Finite.quotient ℤ _
  have hKerSES : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
    abelianGroupRank (LinearMap.range tcLM) +
      abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) :=
    abelianGroupRank_additive (LinearMap.range tcLM).subtype (LinearMap.range tcLM).mkQ
      Subtype.val_injective (Submodule.Quotient.mk_surjective _)
      (by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ _).symm)
  have hQuotEq : abelianGroupRank (↥(AddMonoidHom.ker S.g.hom) ⧸ LinearMap.range tcLM) =
    abelianGroupRank (AddMonoidHom.ker S.g.hom ⧸ AddMonoidHom.range S.abToCycles) := by
    congr 1
  have hKerEq : abelianGroupRank (AddMonoidHom.ker S.g.hom) =
    abelianGroupRank (C.X 0) :=
    abelianGroupRank_eq_of_addEquiv kerEquiv
  have hRangeEq : abelianGroupRank (LinearMap.range tcLM) =
    abelianGroupRank (LinearMap.range (chainDifferentialLinearMap C 0)) := by
    apply abelianGroupRank_eq_of_addEquiv
    have hval : ∀ y : C.X 1,
      (S.abToCycles y : AddMonoidHom.ker S.g.hom).1 =
      chainDifferentialLinearMap C 0 y := by
      intro y; rfl
    refine {
      toFun := fun ⟨a, ha⟩ => ⟨a.1, by
        rw [LinearMap.mem_range] at ha ⊢; obtain ⟨y, hy⟩ := ha
        exact ⟨y, by rw [← hval]; exact congr_arg Subtype.val hy⟩⟩
      invFun := fun ⟨x, hx⟩ => ⟨⟨x, by
        rw [LinearMap.mem_range] at hx; obtain ⟨y, hy⟩ := hx
        rw [← hy, ← hval]; exact (S.abToCycles y).2⟩, by
        rw [LinearMap.mem_range] at hx ⊢; obtain ⟨y, hy⟩ := hx
        exact ⟨y, Subtype.ext (by show (S.abToCycles y).1 = x; rw [hval, hy])⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
    }
  linarith [hKerEq, hKerSES, hQuotEq, hHomRank, hRangeEq]

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_bot
  [AddCommGroup A] :
-- imply
  abelianGroupRank (⊥ : Submodule ℤ A) = 0 := by
-- proof
  have heq : abelianGroupRank (⊥ : Submodule ℤ A) =
    abelianGroupRank (Fin 0 → ℤ) := by
    apply abelianGroupRank_eq_of_addEquiv
    exact {
      toFun := fun _ => Fin.elim0
      invFun := fun _ => 0
      left_inv := fun ⟨x, hx⟩ => by
        simp only [Submodule.mem_bot] at hx; subst hx; rfl
      right_inv := fun f => funext (fun i => Fin.elim0 i)
      map_add' := fun _ _ => by ext i; exact Fin.elim0 i
    }
  rw [heq]
  simp [abelianGroupRank]

end EulerCharacteristic

namespace EulerCharacteristic

/--
[chain_complex_rank_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma chain_complex_rank_decomposition
  {C : ChainComplex AddCommGrpCat ℕ}
  {N : ℕ}
-- given
  (hC_fin : ∀ k, Module.Finite ℤ (C.X k))
  (hC_zero : ∀ m, N ≤ m → IsZero (C.X m)) :
-- imply
  ∃ (rankZ rankB : ℕ → ℕ), (abelianGroupRank (C.X 0) = rankZ 0) ∧ (∀ k, 0 < k → k < N → abelianGroupRank (C.X k) = rankZ k + rankB (k - 1)) ∧ (∀ k, k < N → rankZ k = rankB k + abelianGroupRank (C.homology k)) ∧ (∀ k, N ≤ k + 1 → rankB k = 0) := by
-- proof
  let dk (m : ℕ) : (C.X (m + 1)) →ₗ[ℤ] (C.X m) := chainDifferentialLinearMap C m
  let rB : ℕ → ℕ := fun k => abelianGroupRank (LinearMap.range (dk k))
  let rZ : ℕ → ℕ := fun k =>
    match k with
    | 0 => abelianGroupRank (C.X 0)
    | m + 1 => abelianGroupRank (LinearMap.ker (dk m))
  refine ⟨rZ, rB, rfl, ?_, ?_, ?_⟩
  ·
    intro k hk0 hkN
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp only [rZ, rB]
    exact abelianGroupRank_ker_add_range (dk m)
  ·
    intro k hkN
    match k with
    | 0 =>
      simp only [rZ, rB]
      exact chain_complex_rank_decomposition_zero C hC_fin
    | m + 1 =>
      simp only [rZ, rB]
      exact chain_complex_kernel_image_homology_rank C hC_fin m
  ·
    intro k hk
    show abelianGroupRank (LinearMap.range (dk k)) = 0
    have hzero := hC_zero (k + 1) hk
    have hmorphzero : C.d (k + 1) k = 0 := hzero.eq_of_src _ _
    have hdkzero : dk k = 0 := by
      ext x
      change AddMonoidHom.toIntLinearMap (C.d (k + 1) k).hom x = 0
      rw [hmorphzero]
      simp
    rwa [hdkzero, LinearMap.range_zero]

end EulerCharacteristic

namespace EulerCharacteristic

/--
[cellularChainObj_module_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma cellularChainObj_module_finite
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k : ℕ}
-- given
  (hfin_type : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) :
-- imply
  Module.Finite ℤ ((CWHomology.cellularChainComplex X).X k) := by
-- proof
  change Module.Finite ℤ (CWComplex.cellularChains X k)
  haveI : Finite (Topology.CWComplex.cell (Set.univ : Set X) k) := hfin_type k
  infer_instance

end EulerCharacteristic

namespace EulerCharacteristic

/--
[cellularChainComplex_isZero_above](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma cellularChainComplex_isZero_above
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {N : ℕ}
  {m : ℕ}
-- given
  (hfin_dim : ∀ m, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m))
  (hm : N ≤ m) :
-- imply
  IsZero ((CWHomology.cellularChainComplex X).X m) := by
-- proof
  haveI : IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m) := hfin_dim m hm
  haveI : Subsingleton (CWComplex.cellularChains X m) := inferInstance
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    (show Subsingleton (CWComplex.cellularChains X m) from inferInstance)

end EulerCharacteristic

namespace EulerCharacteristic

/--
[abelianGroupRank_cellularChains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma abelianGroupRank_cellularChains
  {X : Type*}
  [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)]
  {k : ℕ}
-- given
  (hfin : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) :
-- imply
  abelianGroupRank (CWComplex.cellularChains X k) = numCells X k := by
-- proof
  unfold CWComplex.cellularChains numCells
  exact abelianGroupRank_freeAbelianGroup _

end EulerCharacteristic

namespace EulerCharacteristic

/--
[cellular_chain_complex_ranks](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma cellular_chain_complex_ranks
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {N : ℕ}
-- given
  (hfin_dim : ∀ m : ℕ, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m))
  (hfin_type : ∀ n : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) :
-- imply
  ∃ (rankZ rankB : ℕ → ℕ), (numCells X 0 = rankZ 0) ∧ (∀ k, 0 < k → k < N → numCells X k = rankZ k + rankB (k - 1)) ∧ (∀ k, k < N → rankZ k = rankB k + singularHomologyRank X k) ∧ (∀ k, N ≤ k + 1 → rankB k = 0) := by
-- proof
  obtain ⟨rankZ, rankB, h1, h2, h3, h4⟩ := chain_complex_rank_decomposition
    (CWHomology.cellularChainComplex X) N
    (fun k => cellularChainObj_module_finite X hfin_type k)
    (fun m hm => cellularChainComplex_isZero_above X N hfin_dim m hm)
  refine ⟨rankZ, rankB, ?_, ?_, ?_, ?_⟩
  · rw [← abelianGroupRank_cellularChains X hfin_type 0]; exact h1
  · intro k hk0 hkN
    rw [← abelianGroupRank_cellularChains X hfin_type k]; exact h2 k hk0 hkN
  · intro k hkN
    rw [← abelianGroupRank_cellularHomology_eq_singularHomologyRank X k]
    exact h3 k hkN
  · exact h4

end EulerCharacteristic

namespace EulerCharacteristic

/--
[cellular_chain_complex_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma cellular_chain_complex_decomposition
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {N : ℕ}
-- given
  (hfin_dim : ∀ m : ℕ, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m))
  (hfin_type : ∀ n : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) :
-- imply
  ∃ b : ℕ → ℤ, b 0 = 0 ∧ b N = 0 ∧ ∀ k, k < N → (numCells X k : ℤ) = (singularHomologyRank X k : ℤ) + b k + b (k + 1) := by
-- proof
  obtain ⟨rankZ, rankB, hses1_0, hses1, hses2, hbnd⟩ :=
    cellular_chain_complex_ranks X N hfin_dim hfin_type
  let b : ℕ → ℤ := fun k => if k = 0 then 0 else ↑(rankB (k - 1))
  refine ⟨b, ?_, ?_, ?_⟩
  ·
    simp [b]
  ·
    simp only [b]
    by_cases hN : N = 0
    · simp [hN]
    · rw [if_neg hN]
      have := hbnd (N - 1) (by omega)
      simp [this]
  ·
    intro k hk
    simp only [b]
    rw [if_neg (by omega : k + 1 ≠ 0)]
    simp only [Nat.add_sub_cancel]
    by_cases hk0 : k = 0
    ·
      subst hk0
      simp only [ite_true]
      have h1 := hses1_0
      have h2 := hses2 0 hk
      omega
    ·
      rw [if_neg hk0]
      have h1 := hses1 k (by omega) hk
      have h2 := hses2 k hk
      omega

end EulerCharacteristic

namespace EulerCharacteristic

/--
[euler_characteristic_eq_alternating_sum_homology_ranks](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma euler_characteristic_eq_alternating_sum_homology_ranks
  {X : Type}
  [TopologicalSpace X]
  [T2Space X]
  [Topology.CWComplex (Set.univ : Set X)]
  {N : ℕ}
-- given
  (hfin_dim : ∀ m : ℕ, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m))
  (hfin_type : ∀ n : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set X) n)) :
-- imply
  eulerCharacteristic X N = ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * (singularHomologyRank X k : ℤ) := by
-- proof
  obtain ⟨b, hb0, hbN, hdecomp⟩ :=
    cellular_chain_complex_decomposition X N hfin_dim hfin_type
  exact alternating_sum_chain_eq_homology N
    (fun k => (numCells X k : ℤ))
    (fun k => (singularHomologyRank X k : ℤ))
    b hb0 hbN hdecomp

end EulerCharacteristic

namespace EulerCharacteristic

/--
[euler_characteristic_homotopy_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean)
-/
@[path]
lemma euler_characteristic_homotopy_invariant
  {X Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T2Space X]
  [T2Space Y]
  [Topology.CWComplex (Set.univ : Set X)]
  [Topology.CWComplex (Set.univ : Set Y)]
  {N : ℕ}
  {e : ContinuousMap.HomotopyEquiv X Y}
-- given
  (hfin_dim_X : ∀ m, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) m))
  (hfin_type_X : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set X) n))
  (hfin_dim_Y : ∀ m, N ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) m))
  (hfin_type_Y : ∀ n, Finite (Topology.CWComplex.cell (Set.univ : Set Y) n)) :
-- imply
  eulerCharacteristic X N = eulerCharacteristic Y N := by
-- proof
  rw [euler_characteristic_eq_alternating_sum_homology_ranks X N
    hfin_dim_X hfin_type_X,
    euler_characteristic_eq_alternating_sum_homology_ranks Y N
      hfin_dim_Y hfin_type_Y]
  congr 1
  ext k
  congr 1
  exact_mod_cast singularHomologyRank_eq_of_homotopyEquiv e k
/-- Künneth-style identity for Betti numbers under products:
$$\sum_n (-1)^n b_n(X \times Y) = \Bigl(\sum_p (-1)^p b_p(X)\Bigr)
  \Bigl(\sum_q (-1)^q b_q(Y)\Bigr),$$
expressed as a double sum. This is the rank-level shadow of the Künneth
formula and underlies multiplicativity $\chi(X \times Y) = \chi(X) \chi(Y)$. -/
end EulerCharacteristic
namespace CWComplex



-- created on 2026-10-23

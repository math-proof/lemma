-- Carved from Lemma/Definitions/Def_ExtCitation_LocalLevelResidues.lean: instance decls only.
import Mathlib

set_option autoImplicit false

open ExtCitation
open scoped NNReal

namespace ExtCitation.LocalLevel


instance finiteIndex_op_s17 {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [index_op_s17]; exact Subgroup.FiniteIndex.index_ne_zero⟩


instance finiteIndex_fixingSubgroup_s17 {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := by
  let f : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup → E →ₐ[K] L := Quotient.lift
    (fun f ↦ f.toAlgHom.comp E.val)
    (by rintro _ τ ⟨σ, rfl⟩; ext x; exact DFunLike.congr_arg τ (σ.2 x))
  have : Function.Injective f := by
    rintro ⟨σ⟩ ⟨τ⟩ (H : σ.toAlgHom.comp E.val = τ.toAlgHom.comp E.val)
    refine Quotient.sound ⟨⟨.op (τ⁻¹ * σ), fun x ↦ ?_⟩, by simp⟩
    simpa [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] using DFunLike.congr_fun H x
  have := Finite.of_injective _ this
  exact Subgroup.finiteIndex_of_finite_quotient

open IntermediateField in
instance compactSpace_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    CompactSpace (L ≃ₐ[K] L) := by
  classical
  letI := IsTopologicalGroup.rightUniformSpace (L ≃ₐ[K] L)
  rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete]
  refine ⟨totallyBounded_s17 fun s hs ↦ ?_, ?_⟩
  · obtain ⟨E, hE, H⟩ := (krullTopology_mem_nhds_one_iff _ _ _).mp hs
    refine ⟨_, inferInstance, H⟩
  · rintro f hf -
    have := hf.1
    have (x : L) :
        ∃ σ₀ : L ≃ₐ[K] L, ∃ t ∈ f, ∀ σ ∈ t, ∀ τ : L ≃ₐ[K] L, σ (τ x) = σ₀ (τ x) := by
      have : FiniteDimensional K K⟮x⟯ :=
        adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      obtain ⟨t, htf, H⟩ := ((Filter.HasBasis.cauchy_iff
        (by exact (galGroupBasis K L).nhds_one_hasBasis.comap _)).mp hf).2 _ (by
            exact ⟨_, ⟨normalClosure K K⟮x⟯ L, inferInstanceAs (FiniteDimensional K _), rfl⟩, rfl⟩)
      obtain ⟨σ, hσ⟩ := f.nonempty_of_mem htf
      refine ⟨σ, t, htf, fun τ hτ τ₀ ↦ ?_⟩
      have : σ (τ.symm (τ (τ₀ x))) = τ (τ₀ x) := H τ hτ σ hσ ⟨τ (τ₀ x), by
        refine SetLike.le_def.mp (le_iSup _ (τ.toAlgHom.comp <| τ₀.toAlgHom.comp (val _))) ?_
        exact ⟨⟨_, subset_adjoin _ _ (by simp)⟩, rfl⟩⟩
      simpa using this.symm
    choose σ₀ t htf H using this
    have H' (s σ hσ) := H s σ hσ .refl
    dsimp at H'
    let F : L ≃ₐ[K] L :=
    { toFun x := σ₀ x x
      invFun x := (σ₀ x).symm x
      left_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf (σ₀ x x)))
        dsimp
        have H' := H' _ _ hσ₁
        have : σ x = (σ₀ (σ₀ x x) x) := by simpa using H _ _ hσ₂ (σ₀ x).symm
        rw [← H', AlgEquiv.symm_apply_eq, H', ← this, H']
      right_inv x := by
        obtain ⟨σ, hσ₁, hσ₂⟩ := f.nonempty_of_mem (f.inter_mem (htf x) (htf ((σ₀ x).symm x)))
        dsimp
        replace H := H _ _ hσ₁ σ.symm
        simp only [AlgEquiv.apply_symm_apply, ← AlgEquiv.symm_apply_eq, AlgEquiv.symm_symm] at H
        rw [← H' _ _ hσ₂, H]
      map_mul' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x * y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_mul]
      map_add' x y := by
        obtain ⟨σ, hσx, hσy, hσxy⟩ :=
          f.nonempty_of_mem (f.inter_mem (htf x) (f.inter_mem (htf y) (htf (x + y))))
        rw [← H' _ _ hσxy, ← H' _ _ hσx, ← H' _ _ hσy, map_add]
      commutes' := by simp }
    refine ⟨F, Set.mem_univ _, ?_⟩
    rw [((galGroupBasis K L).nhds_hasBasis F).ge_iff]
    rintro _ ⟨_, ⟨E, hE, rfl⟩, rfl⟩
    simp only [Set.image_mul_left]
    have ⟨s, hs⟩ := E.toSubmodule.fg_iff_finiteDimensional.mpr hE
    refine f.mem_of_superset ((Filter.biInter_finset_mem s).mpr fun i _ ↦ htf i) ?_
    rintro σ hσ ⟨x, hx⟩
    change F.symm (σ x) = x
    induction hs.ge hx using Submodule.span_induction with
    | zero | add | smul => simp_all
    | mem x h =>
      rw [AlgEquiv.symm_apply_eq]
      simp [F, ← H' _ _ (Set.mem_iInter₂.mp hσ _ h)]

open scoped IntermediateField in
instance continuousSMulDiscrete_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) L := by
  constructor
  intro x y
  rw [isOpen_iff_forall_mem_open]
  rintro σ (hσ : _ = _)
  have : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  refine ⟨_, ?_, K⟮x⟯.fixingSubgroup_isOpen.smul σ, 1, one_mem _, by simp⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have := (mem_fixingSubgroup_iff _).mp hτ x (IntermediateField.mem_adjoin_simple_self K x)
  simp only [smul_eq_mul, Set.mem_setOf_eq, mul_smul, this, hσ]

instance isInvariant_gal {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) :=
  ⟨fun _ H ↦ (InfiniteGalois.fixedField_fixingSubgroup
    (⊥ : IntermediateField K L)).le fun _ ↦ H _⟩

section Local

variable (q : ℕ) [Fact q.Prime]


noncomputable instance smulOO : SMul (GG q) (OO q) :=
  ⟨fun g x => ⟨g (x : PadicAlgCl q), by
    rw [mem_padicIntegers_iff, nnnorm_padicAlgCl_algEquiv]; exact (mem_padicIntegers_iff q).mp x.2⟩⟩


noncomputable instance actOO : MulSemiringAction (GG q) (OO q) where
  one_smul x := Subtype.ext rfl
  mul_smul g h x := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g x y := Subtype.ext (map_add g _ _)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g x y := Subtype.ext (map_mul g _ _)


noncomputable instance algOO : Algebra ℤ_[q] (OO q) := (intToOO q).toAlgebra


instance smulCommOO : SMulCommClass (GG q) ℤ_[q] (OO q) where
  smul_comm g r x := by
    apply Subtype.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change g ((algebraMap ℤ_[q] (OO q) r : PadicAlgCl q) * (x : PadicAlgCl q))
      = (algebraMap ℤ_[q] (OO q) r : PadicAlgCl q) * g (x : PadicAlgCl q)
    rw [map_mul, algebraMap_OO_coe, AlgEquiv.commutes]

instance isInvariantOO : Algebra.IsInvariant ℤ_[q] (OO q) (GG q) where
  isInvariant b hb := by
    haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
    have hb' : ∀ g : GG q, g • (b : PadicAlgCl q) = b := fun g => congrArg Subtype.val (hb g)
    obtain ⟨x, hx⟩ := Algebra.IsInvariant.isInvariant (A := ℚ_[q]) (G := GG q) (b : PadicAlgCl q) hb'
    have hx1 : ‖x‖ ≤ 1 := by
      rw [← PadicAlgCl.norm_extends]
      change ‖algebraMap ℚ_[q] (PadicAlgCl q) x‖ ≤ 1
      rw [hx]
      have := (mem_padicIntegers_iff q).mp b.2
      exact_mod_cast this
    exact ⟨⟨x, hx1⟩, Subtype.ext hx⟩

instance csdOO : ContinuousSMulDiscrete (GG q) (OO q) := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro x
  have : (MulAction.stabilizer (GG q) x : Set (GG q)) = MulAction.stabilizer (GG q) (x : PadicAlgCl q) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [this]
  exact ContinuousSMulDiscrete.isOpen_stabilizer (GG q) (x : PadicAlgCl q)


end Local


section LevelW

variable (q : ℕ) [Fact q.Prime]
variable (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]


noncomputable instance algRwOO : Algebra (Rw q Kw) (OO q) := (RwToOO q Kw).toAlgebra


instance smulCommRw : SMulCommClass (Gw q Kw) (Rw q Kw) (OO q) where
  smul_comm g r x := by
    apply Subtype.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change (g : GG q) ((algebraMap (Rw q Kw) (OO q) r : PadicAlgCl q) * (x : PadicAlgCl q))
      = (algebraMap (Rw q Kw) (OO q) r : PadicAlgCl q) * (g : GG q) (x : PadicAlgCl q)
    rw [map_mul, algebraMap_Rw_coe]
    congr 1
    exact (IntermediateField.mem_fixingSubgroup_iff Kw (g : GG q)).mp g.2 _ (r : Kw).2

instance isInvariantRw : Algebra.IsInvariant (Rw q Kw) (OO q) (Gw q Kw) where
  isInvariant b hb := by
    haveI : IsGalois ℚ_[q] (PadicAlgCl q) := IsAlgClosure.isGalois ℚ_[q] (PadicAlgCl q)
    have hb' : (b : PadicAlgCl q) ∈ IntermediateField.fixedField (Gw q Kw) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact congrArg Subtype.val (hb ⟨g, hg⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hb'
    refine ⟨⟨⟨(b : PadicAlgCl q), hb'⟩, ?_⟩, Subtype.ext rfl⟩
    show algebraMap Kw (PadicAlgCl q) ⟨(b : PadicAlgCl q), hb'⟩ ∈ padicIntegers q
    exact b.2

instance csdRw : ContinuousSMulDiscrete (Gw q Kw) (OO q) := by
  rw [continuousSMulDiscrete_iff_isOpen_stabilizer]
  intro x
  have : (MulAction.stabilizer (Gw q Kw) x : Set (Gw q Kw))
      = Subtype.val ⁻¹' (MulAction.stabilizer (GG q) x : Set (GG q)) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rfl
  rw [this]
  exact (ContinuousSMulDiscrete.isOpen_stabilizer (GG q) x).preimage continuous_subtype_val

instance compactGw : CompactSpace (Gw q Kw) :=
  isCompact_iff_compactSpace.mp (Kw.fixingSubgroup_isClosed.isCompact)


end LevelW

section Residues

variable (q : ℕ) [Fact q.Prime]


instance charP_kbar : CharP (kbar q) q :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr (natCast_residue_eq_zero q)

noncomputable instance algZModKbar : Algebra (ZMod q) (kbar q) := ZMod.algebra (kbar q) q


end Residues


end ExtCitation.LocalLevel

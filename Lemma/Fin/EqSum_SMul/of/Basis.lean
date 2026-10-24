import Mathlib
import sympy.Basic
import sympy.algebra.lie.levi_decomposition
open LeviDecomposition
open LieAlgebra


/--
[levi_sum_repr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
@[path]
private lemma main
  [Semiring K] [AddCommMonoid V] [Module K V] [Fintype ι]
-- given
  (b : Module.Basis ι K V) (x : V) :
-- imply
  ∑ i, b.repr x i • b i = x := by
-- proof
  apply b.repr.injective
  ext j
  simp



/--
[levi_repr_eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_repr_eq_dual
  [Field K] [AddCommGroup V] [Module K V] [Finite ι] [DecidableEq ι]
-- given
  (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
  (b : Module.Basis ι K V) (x : V) (i : ι) :
-- imply
  b.repr x i = B (B.dualBasis hB b i) x := by
-- proof
  let _ := Fintype.ofFinite ι
  conv_rhs => rw [← levi_sum_repr b x]
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_left hB b]
  simp



/--
[leviTraceKernel_isSolvable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviTraceKernel_isSolvable
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] [LieModule.IsFaithful K L M] :
-- imply
  LieAlgebra.IsSolvable (leviTraceKernel (K := K) (L := L) (M := M)) := by
-- proof
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  change LieAlgebra.IsSolvable I
  have htf : LieModule.traceForm K I M = 0 := by
    ext x y
    change LieModule.traceForm K L M x.1 y.1 = 0
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp x.2) y
  let D' := LieAlgebra.derivedSeries K I 1
  have hnil : LieModule.IsNilpotent D' M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero htf
  let D : LieIdeal K L := ⁅I, I⁆
  have hnil' (x : D) : IsNilpotent (LieModule.toEnd K D M x) := by
    have hxI : x.1 ∈ I := LieSubmodule.lie_le_left I I x.2
    have hxD' : (⟨x.1, hxI⟩ : I) ∈ LieAlgebra.derivedSeries K I 1 := by
      rwa [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
    let x' : D' := ⟨⟨x.1, hxI⟩, hxD'⟩
    have hx := (LieModule.isNilpotent_iff_forall' (R := K)).mp hnil x'
    change IsNilpotent (LieModule.toEnd K L M x.1)
    change IsNilpotent (LieModule.toEnd K L M x'.1.1) at hx
    simpa [x'] using hx
  let φ := LieModule.toEnd K D M
  have hrange : LieRing.IsNilpotent φ.range := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := K) (L := φ.range)]
    rintro ⟨_, ⟨x, rfl⟩⟩
    apply LieAlgebra.isNilpotent_ad_of_isNilpotent
    exact hnil' x
  let _ : LieRing.IsNilpotent φ.range := hrange
  have hφ : Function.Injective φ.rangeRestrict := by
    intro x y hxy
    apply Subtype.ext
    apply LieModule.IsFaithful.injective_toEnd (R := K) (L := L) (M := M)
    exact congr_arg Subtype.val hxy
  have hD : LieRing.IsNilpotent D := hφ.lieAlgebra_isNilpotent
  let _ : LieRing.IsNilpotent D := hD
  let _ : LieAlgebra.IsSolvable D := inferInstance
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K D
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) D] at hk
  change LieAlgebra.derivedSeriesOfIdeal K L k ⁅I, I⁆ = ⊥ at hk
  refine LieAlgebra.IsSolvable.mk (R := K) (L := I) (k := k + 1) ?_
  rw [LieIdeal.derivedSeries_eq_bot_iff (R := K) (L := L) I]
  rwa [LieAlgebra.derivedSeriesOfIdeal_add, LieAlgebra.derivedSeriesOfIdeal_succ,
    LieAlgebra.derivedSeriesOfIdeal_zero]



/--
[levi_traceForm_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_traceForm_nondegenerate
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
  [LieModule.IsFaithful K L M] :
-- imply
  (LieModule.traceForm K L M).Nondegenerate := by
-- proof
  let I := leviTraceKernel (K := K) (L := L) (M := M)
  have hsolv : LieAlgebra.IsSolvable I := leviTraceKernel_isSolvable
  let _ : LieAlgebra.IsSolvable I := hsolv
  have hI : I = ⊥ := LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable I
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  change (I : Submodule K L) = ⊥
  exact congr_arg LieSubmodule.toSubmodule hI



/--
[levi_trace_casimir](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_trace_casimir
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate) :
-- imply
  LinearMap.trace K M (leviCasimir hβ) = (Module.finrank K L : K) := by
-- proof
  classical
  let b := Module.Free.chooseBasis K L
  change LinearMap.trace K M (∑ i, LieModule.toEnd K L M (b i) *
    LieModule.toEnd K L M ((LieModule.traceForm K L M).dualBasis hβ b i)) = _
  rw [map_sum]
  simp_rw [Module.End.mul_eq_comp]
  simp_rw [← LieModule.traceForm_apply_apply]
  simp_rw [LinearMap.BilinForm.apply_dualBasis_right hβ
    (LinearMap.BilinForm.isSymm_iff.mpr (LieModule.traceForm_isSymm K L M)) b]
  simp [Module.finrank_eq_card_basis b]



/--
[levi_lie_dualBasis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_lie_dualBasis
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Fintype ι] [DecidableEq ι]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate)
  (b : Module.Basis ι K L) (x : L) (i : ι) :
-- imply
  Bracket.bracket x ((LieModule.traceForm K L M).dualBasis hβ b i) =
    -∑ j, b.repr (Bracket.bracket x (b j)) i •
      (LieModule.traceForm K L M).dualBasis hβ b j := by
-- proof
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  apply d.repr.injective
  ext j
  rw [LinearMap.BilinForm.dualBasis_repr_apply]
  rw [LieModule.traceForm_apply_lie_apply']
  rw [← levi_repr_eq_dual hβ b ⁅x, b j⁆ i]
  simp [d, Finsupp.single_apply]



/--
[levi_casimir_commute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_casimir_commute
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (hβ : (LieModule.traceForm K L M).Nondegenerate) (x : L) :
-- imply
  Commute (leviCasimir hβ) (LieModule.toEnd K L M x) := by
-- proof
  classical
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  let ρ := LieModule.toEnd K L M
  change Commute (∑ i, ρ (b i) * ρ (d i)) (ρ x)
  rw [commute_iff_eq]
  rw [← sub_eq_zero]
  calc
    (∑ i, ρ (b i) * ρ (d i)) * ρ x - ρ x * (∑ i, ρ (b i) * ρ (d i)) =
      -(∑ i, (ρ ⁅x, b i⁆ * ρ (d i) + ρ (b i) * ρ ⁅x, d i⁆)) := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [LieHom.map_lie ρ, LieHom.map_lie ρ, Ring.lie_def, Ring.lie_def]
        noncomm_ring
    _ = 0 := by
      have hxb (i) : ρ ⁅x, b i⁆ =
        ∑ j, b.repr ⁅x, b i⁆ j • ρ (b j) := by
        conv_lhs => rw [← levi_sum_repr b ⁅x, b i⁆]
        rw [map_sum]
        simp_rw [map_smul]
      have hxd (i) : ρ ⁅x, d i⁆ =
        -∑ j, b.repr ⁅x, b j⁆ i • ρ (d j) := by
        rw [levi_lie_dualBasis hβ b x i]
        rw [map_neg, map_sum]
        simp_rw [map_smul]
        rfl
      rw [Finset.sum_add_distrib]
      simp_rw [hxb, hxd]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
        mul_neg, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp



/--
[levi_casimir_range_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_casimir_range_le
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
-- given
  (W : Submodule K M) (hβ : (LieModule.traceForm K L M).Nondegenerate)
  (hW : ∀ (x : L) (m : M), LieModule.toEnd K L M x m ∈ W) :
-- imply
  LinearMap.range (leviCasimir hβ) ≤ W := by
-- proof
  classical
  rintro _ ⟨m, rfl⟩
  let b := Module.Free.chooseBasis K L
  let d := (LieModule.traceForm K L M).dualBasis hβ b
  change (∑ i, LieModule.toEnd K L M (b i) * LieModule.toEnd K L M (d i)) m ∈ W
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  rw [Module.End.mul_apply]
  exact hW (b i) _



/--
[levi_isKilling_killingCompl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isKilling_killingCompl
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L]
-- given
  (I : LieIdeal K L) :
-- imply
  LieAlgebra.IsKilling K I.killingCompl := by
-- proof
  let _ : LieAlgebra.IsKilling K L := inferInstance
  let H := I.killingCompl
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hB := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  have hrefl := (LieModule.traceForm_isSymm K L L).isRefl
  have horth : (killingForm K L).orthogonal H.toSubmodule = I.toSubmodule := by
    change (killingForm K L).orthogonal
      ((killingForm K L).orthogonal I.toSubmodule) = I.toSubmodule
    exact LinearMap.BilinForm.orthogonal_orthogonal hB hrefl I.toSubmodule
  have hdisj : Disjoint H.toSubmodule
    ((killingForm K L).orthogonal H.toSubmodule) := by
    rw [horth]
    exact LieSubmodule.disjoint_toSubmodule.mpr hcompl.disjoint.symm
  have hres : ((killingForm K L).restrict H.toSubmodule).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
      (killingForm K L) hrefl hdisj
  have hk : (killingForm K H).Nondegenerate := by
    rwa [LieIdeal.killingForm_eq]
  refine LieAlgebra.IsKilling.mk ?_
  rw [eq_bot_iff]
  intro x hx
  rw [LieSubmodule.mem_bot]
  apply hk.2 x
  intro y
  exact (LieIdeal.mem_killingCompl K H ⊤).mp hx y (LieSubmodule.mem_top y)



/--
[levi_isFaithful_killingCompl_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isFaithful_killingCompl_ker
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] :
-- imply
  LieModule.IsFaithful K (LieModule.ker K L M).killingCompl M := by
-- proof
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  refine ⟨?_⟩
  intro x y hxy
  apply Subtype.ext
  change LieModule.toEnd K L M x.1 = LieModule.toEnd K L M y.1 at hxy
  have hker : x.1 - y.1 ∈ I := by
    change LieModule.toEnd K L M (x.1 - y.1) = 0
    rwa [map_sub, sub_eq_zero]
  have hH : x.1 - y.1 ∈ H := H.sub_mem x.2 y.2
  have hz : x.1 - y.1 ∈ I ⊓ H := ⟨hker, hH⟩
  rw [hcompl.inf_eq_bot] at hz
  change x.1 - y.1 = 0 at hz
  exact sub_eq_zero.mp hz



/--
[levi_lie_top_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_lie_top_eq_top
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSemisimple K L] :
-- imply
  Bracket.bracket (⊤ : LieIdeal K L) (⊤ : LieIdeal K L) = ⊤ := by
-- proof
  apply top_unique
  calc
    (⊤ : LieIdeal K L) = sSup {I : LieIdeal K L | IsAtom I} :=
      LieAlgebra.IsSemisimple.sSup_atoms_eq_top.symm
    _ ≤ ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := by
      apply sSup_le
      intro I hI
      rw [← lie_eq_self_of_isAtom_of_nonabelian I hI
        (LieAlgebra.IsSemisimple.non_abelian_of_isAtom I hI)]
      exact LieSubmodule.mono_lie le_top le_top



/--
[levi_codim_one_action_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_codim_one_action_mem
  [Field K] [LieRing L] [LieAlgebra K L] [LieAlgebra.IsSemisimple K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hW : Module.finrank K (M ⧸ W) = 1) :
-- imply
  ∀ (x : L) (m : M), Bracket.bracket x m ∈ W := by
-- proof
  let Q := M ⧸ W
  have hendcomm (f g : Module.End K Q) : Commute f g := by
    obtain ⟨a, ha, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW f
    obtain ⟨b, hb, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW g
    rw [ha, hb]
    ext q
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm]
  have hbracket (x y : L) : LieModule.toEnd K L Q ⁅x, y⁆ = 0 := by
    rw [LieHom.map_lie, Ring.lie_def, (hendcomm _ _).eq, sub_self]
  have hle : ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ≤ LieModule.ker K L Q := by
    rw [LieSubmodule.lie_le_iff]
    intro x _ y _
    change LieModule.toEnd K L Q ⁅x, y⁆ = 0
    exact hbracket x y
  have hker : LieModule.ker K L Q = ⊤ := by
    apply top_unique
    rwa [← levi_lie_top_eq_top]
  intro x m
  apply (LieSubmodule.Quotient.mk_eq_zero W).mp
  rw [LieModuleHom.map_lie]
  have hx : x ∈ LieModule.ker K L Q := by
    rw [hker]
    exact LieSubmodule.mem_top x
  change LieModule.toEnd K L Q x ((LieSubmodule.Quotient.mk' W) m) = 0
  change LieModule.toEnd K L Q x = 0 at hx
  rw [hx]
  rfl



/--
[levi_exists_isCompl_of_trivial_action](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_exists_isCompl_of_trivial_action
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (htriv : ∀ (x : L) (m : M), Bracket.bracket x m = 0) (W : LieSubmodule K L M) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  obtain ⟨U, hU⟩ := W.toSubmodule.exists_isCompl
  let U' : LieSubmodule K L M :=
    { __ := U
      lie_mem := by
        intro x m _
        rw [htriv]
        exact zero_mem U }
  exact ⟨U', LieSubmodule.isCompl_toSubmodule.mp hU⟩



/--
[levi_finrank_quotient_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_finrank_quotient_comap
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (V W : LieSubmodule K L M) (hVW : V ⊔ W = ⊤) :
-- imply
  Module.finrank K (V ⧸ W.comap V.incl) = Module.finrank K (M ⧸ W) := by
-- proof
  change Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
    Module.finrank K (M ⧸ W.toSubmodule)
  let f : V →ₗ[K] M ⧸ W := W.toSubmodule.mkQ.comp V.toSubmodule.subtype
  have hker : LinearMap.ker f = (W.comap V.incl).toSubmodule := by
    ext v
    simp [f]
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ m =>
      have hm : m ∈ V ⊔ W := by
        rw [hVW]
        exact LieSubmodule.mem_top m
      rw [LieSubmodule.mem_sup] at hm
      obtain ⟨v, hv, w, hw, rfl⟩ := hm
      refine ⟨⟨v, hv⟩, ?_⟩
      change LieSubmodule.Quotient.mk (N := W) v =
        LieSubmodule.Quotient.mk (N := W) (v + w)
      apply (Submodule.Quotient.eq W.toSubmodule).2
      have hw' : w ∈ W.toSubmodule := hw
      simpa only [sub_add_cancel_left, neg_mem_iff] using hw'
  calc
    Module.finrank K (V ⧸ (W.comap V.incl).toSubmodule) =
      Module.finrank K (V ⧸ LinearMap.ker f) := by rw [hker]
    _ = Module.finrank K (LinearMap.range f) := f.quotKerEquivRange.finrank_eq
    _ = Module.finrank K (M ⧸ W) := by
      exact (LinearEquiv.ofTop (LinearMap.range f)
        (LinearMap.range_eq_top.mpr hsurj)).finrank_eq



/--
[levi_isCompl_map_of_isCompl_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isCompl_map_of_isCompl_comap
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (V W : LieSubmodule K L M) (U : LieSubmodule K L V) (hVW : V ⊔ W = ⊤)
  (hU : IsCompl (W.comap V.incl) U) :
-- imply
  IsCompl W (U.map V.incl) := by
-- proof
  constructor
  · rw [disjoint_iff]
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxU⟩ := hx
    change x ∈ U.toSubmodule.map V.toSubmodule.subtype at hxU
    rw [Submodule.mem_map] at hxU
    obtain ⟨u, hu, rfl⟩ := hxU
    have huW : u ∈ W.comap V.incl := hxW
    have hu0 : u ∈ (W.comap V.incl) ⊓ U := ⟨huW, hu⟩
    rw [hU.inf_eq_bot] at hu0
    change u = 0 at hu0
    change (u.1 : M) = 0
    exact congr_arg Subtype.val hu0
  · rw [codisjoint_iff]
    apply top_unique
    intro x _
    have hx : x ∈ V ⊔ W := by
      rw [hVW]
      exact LieSubmodule.mem_top x
    rw [LieSubmodule.mem_sup] at hx
    obtain ⟨v, hv, w, hw, rfl⟩ := hx
    let v' : V := ⟨v, hv⟩
    have hv' : v' ∈ (W.comap V.incl) ⊔ U := by
      rw [hU.sup_eq_top]
      exact LieSubmodule.mem_top v'
    rw [LieSubmodule.mem_sup] at hv'
    obtain ⟨a, ha, b, hb, hab⟩ := hv'
    rw [LieSubmodule.mem_sup]
    refine ⟨a.1 + w, W.add_mem ha hw, b.1, ?_, ?_⟩
    · exact LieSubmodule.mem_map_of_mem hb
    · apply_fun Subtype.val at hab
      dsimp [v'] at hab
      rw [← hab]
      abel



/--
[levi_codim_one_complement_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_codim_one_complement_aux
  (n : ℕ) {K L M : Type*} [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] (W : LieSubmodule K L M)
  (hquot : Module.finrank K (M ⧸ W) = 1) (_hlt : Module.finrank K W < n) :
  ∃ U : LieSubmodule K L M, IsCompl W U := by
  classical
  let I := LieModule.ker K L M
  let H := I.killingCompl
  let _ : LieAlgebra.IsKilling K L := inferInstance
  have hcompl : IsCompl I H := I.isCompl_killingCompl
  have hHkilling : LieAlgebra.IsKilling K H := levi_isKilling_killingCompl I
  let _ : LieAlgebra.IsKilling K H := hHkilling
  let _ : LieAlgebra.IsSemisimple K H := inferInstance
  by_cases hH0 : Module.finrank K H = 0
  · have hHbot : H = ⊥ := by
    rw [← LieSubmodule.toSubmodule_inj]
    exact Submodule.finrank_eq_zero.mp hH0
    have hItop : I = ⊤ := by
      have hs := hcompl.sup_eq_top
      rwa [hHbot, sup_bot_eq] at hs
    apply levi_exists_isCompl_of_trivial_action (W := W)
    intro x m
    have hx : x ∈ I := by
      rw [hItop]
      exact LieSubmodule.mem_top x
    change LieModule.toEnd K L M x = 0 at hx
    change LieModule.toEnd K L M x m = 0
    rw [hx]
    rfl
  · have hfaithful : LieModule.IsFaithful K H M :=
    levi_isFaithful_killingCompl_ker
    let _ : LieModule.IsFaithful K H M := hfaithful
    have hβ : (LieModule.traceForm K H M).Nondegenerate :=
      levi_traceForm_nondegenerate
    let c := leviCasimir hβ
    have hcL (x : L) : Commute c (LieModule.toEnd K L M x) := by
      have hx : x ∈ I ⊔ H := by
        rw [hcompl.sup_eq_top]
        exact LieSubmodule.mem_top x
      rw [LieSubmodule.mem_sup] at hx
      obtain ⟨i, hi, h, hh, rfl⟩ := hx
      have hi0 : LieModule.toEnd K L M i = 0 := by
        exact hi
      have hch := levi_casimir_commute hβ (⟨h, hh⟩ : H)
      change Commute c (LieModule.toEnd K L M h) at hch
      rwa [map_add, hi0, zero_add]
    let V := leviZeroFitting c hcL
    let P := ⨅ k : ℕ, LinearMap.range (c ^ k)
    have hV : V.toSubmodule = ⨆ k : ℕ, LinearMap.ker (c ^ k) := by
      change c.maxGenEigenspace 0 = _
      rw [← Module.End.iSup_genEigenspace_eq]
      simp_rw [Module.End.genEigenspace_zero_nat]
    have hVP : IsCompl V.toSubmodule P := by
      rw [hV]
      exact LinearMap.isCompl_iSup_ker_pow_iInf_range_pow c
    have haction := levi_codim_one_action_mem W hquot
    have hcW : LinearMap.range c ≤ W.toSubmodule := by
      apply levi_casimir_range_le hβ W.toSubmodule
      intro x m
      exact haction x.1 m
    have hPW : P ≤ W.toSubmodule := by
      calc
        P ≤ LinearMap.range (c ^ 1) := iInf_le _ 1
        _ = LinearMap.range c := by rw [pow_one]
        _ ≤ W.toSubmodule := hcW
    have hPne : P ≠ ⊥ := by
      intro hP
      have hVtop : V.toSubmodule = ⊤ := by
        have hs := hVP.sup_eq_top
        rwa [hP, sup_bot_eq] at hs
      have hpoint : ∀ m : M, ∃ k : ℕ, (c ^ k) m = 0 := by
        intro m
        have hm : m ∈ c.maxGenEigenspace 0 := by
          change m ∈ V.toSubmodule
          rwa [hVtop]
        simpa using (Module.End.mem_maxGenEigenspace c 0 m).mp hm
      have hnil : IsNilpotent c :=
        ((LinearMap.charpoly_nilpotent_tfae c).out 3 1).mp hpoint
      have htrace0 : LinearMap.trace K M c = 0 :=
        (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
      rw [levi_trace_casimir hβ] at htrace0
      exact (Nat.cast_ne_zero.mpr hH0) htrace0
    have hVWsub : V.toSubmodule ⊔ W.toSubmodule = ⊤ := by
      apply top_unique
      rw [← hVP.sup_eq_top]
      exact sup_le_sup le_rfl hPW
    have hVW : V ⊔ W = ⊤ := by
      rwa [← LieSubmodule.toSubmodule_inj]
    have hInfLt : V.toSubmodule ⊓ W.toSubmodule < W.toSubmodule := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      have hWV : W.toSubmodule ≤ V.toSubmodule := by
        rwa [← heq]
      have hPV : P ≤ V.toSubmodule := hPW.trans hWV
      apply hPne
      rw [← le_bot_iff, ← hVP.inf_eq_bot]
      exact le_inf hPV le_rfl
    let W' := W.comap V.incl
    have hmapW' : W'.map V.incl = V ⊓ W := by
      ext x
      constructor
      · intro hx
        rw [LieSubmodule.mem_map] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact ⟨w.2, hw⟩
      · rintro ⟨hxV, hxW⟩
        exact LieSubmodule.mem_map_of_mem (m := (⟨x, hxV⟩ : V)) hxW
    have hfinW' : Module.finrank K W' = Module.finrank K ↑(V ⊓ W) := by
      rw [← hmapW']
      exact (LieSubmodule.equivMapOfInjective W' V.injective_incl).toLinearEquiv.finrank_eq
    have hlt' : Module.finrank K W' < Module.finrank K W := by
      rw [hfinW']
      exact Submodule.finrank_lt_finrank_of_lt hInfLt
    have hquot' : Module.finrank K (V ⧸ W') = 1 := by
      rwa [levi_finrank_quotient_comap V W hVW]
    obtain ⟨U, hU⟩ := levi_codim_one_complement_aux (Module.finrank K W) W' hquot' hlt'
    exact ⟨U.map V.incl, levi_isCompl_map_of_isCompl_comap V W hVW U hU⟩
termination_by n
decreasing_by exact _hlt



/--
[levi_codim_one_complement](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_codim_one_complement
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieAlgebra.IsSemisimple K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hquot : Module.finrank K (M ⧸ W) = 1) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U :=
-- proof
  levi_codim_one_complement_aux (Module.finrank K W + 1) W hquot (Nat.lt_succ_self _)



/--
[leviHomScalar_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviHomScalar_apply
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) (f : leviHomScalarMaps W) (w : W) :
-- imply
  f.1 w = leviHomScalar W hW f • w :=
-- proof
  Classical.choose_spec f.2 w



/--
[levi_lie_mem_HomVanishing_of_mem_scalarMaps](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_lie_mem_HomVanishing_of_mem_scalarMaps
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (f : leviHomScalarMaps W) (x : L) :
-- imply
  Bracket.bracket x (f.1 : M →ₗ[K] W) ∈ leviHomVanishing W := by
-- proof
  obtain ⟨a, ha⟩ := f.2
  intro w
  rw [LieHom.lie_apply, ha, lie_smul]
  have haw := ha (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W)
  rw [haw]
  have hxw : ⁅x, w⁆ = (⟨⁅x, w.1⁆, W.lie_mem w.2⟩ : W) := rfl
  rw [hxw, sub_self]



/--
[leviFactorLieModule](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviFactorLieModule
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) :
-- imply
  @LieModule K (L ⧸ I) M _ _ _ _ _ (leviFactorLieRingModule I hI) :=
-- proof
  LieModule.compLieHom M (leviFactorAction I hI)



/--
[levi_factor_exists_isCompl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_factor_exists_isCompl
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
-- given
  (I : LieIdeal K L) (hI_semisimple : LieAlgebra.IsSemisimple K (L ⧸ I))
  (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) (W : LieSubmodule K L M) :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  have := hI_semisimple
  let _ := leviFactorLieRingModule I hI
  let _ := leviFactorLieModule I hI
  obtain ⟨U, hU⟩ :=
    LieModule.exists_isCompl_of_isSemisimple (leviFactorSubmodule I hI W)
  refine ⟨leviUnfactorSubmodule I hI U, ?_⟩
  rwa [← LieSubmodule.isCompl_toSubmodule] at hU ⊢



/--
[leviQuotientMk_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviQuotientMk_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) :
-- imply
  Function.Surjective (leviQuotientMk I) := by
-- proof
  intro y
  obtain ⟨x, hx⟩ := LieSubmodule.Quotient.surjective_mk' I y
  exact ⟨x, (leviQuotientMk_apply I x).trans hx⟩
@[simp] private theorem leviQuotientMk_ker
  {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
  (I : LieIdeal K L) : (leviQuotientMk I).ker = I := by
  ext x
  rw [LieHom.mem_ker, leviQuotientMk_apply]
  exact LieSubmodule.Quotient.mk_eq_zero (N := I)



/--
[levi_isSolvable_of_ker_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isSolvable_of_ker_quotient
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L'] [LieAlgebra.IsSolvable L']
-- given
  (f : LieHom K L L') (hker : LieAlgebra.IsSolvable f.ker)
  (hf : Function.Surjective f) :
-- imply
  LieAlgebra.IsSolvable L := by
-- proof
  have := hker
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K L'
  obtain ⟨l, hl⟩ := LieAlgebra.IsSolvable.solvable K f.ker
  apply LieAlgebra.IsSolvable.mk (R := K) (L := L) (k := l + k)
  change LieAlgebra.derivedSeriesOfIdeal K L (l + k) ⊤ = ⊥
  rw [LieAlgebra.derivedSeriesOfIdeal_add]
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hl
  apply le_bot_iff.mp
  rw [← hl]
  apply LieAlgebra.derivedSeriesOfIdeal_mono
  rw [← LieIdeal.map_eq_bot_iff]
  rw [LieIdeal.derivedSeries_map_eq k hf, hk]



/--
[leviComapMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviComapMap_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (J : LieIdeal K L') :
-- imply
  Function.Surjective (leviComapMap f J) := by
-- proof
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxJ : x ∈ J.comap f := by
    change f x ∈ J
    rwa [hx]
  refine ⟨⟨x, hxJ⟩, ?_⟩
  apply Subtype.ext
  exact hx



/--
[leviComapMapKerToKer_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviComapMapKerToKer_injective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (J : LieIdeal K L') :
-- imply
  Function.Injective (leviComapMapKerToKer f J) := by
-- proof
  intro x y h
  have hxy := congrArg (fun z : f.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)



/--
[levi_isSolvable_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isSolvable_comap
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hker : LieAlgebra.IsSolvable f.ker) (hf : Function.Surjective f)
  (J : LieIdeal K L') [LieAlgebra.IsSolvable J] :
-- imply
  LieAlgebra.IsSolvable (J.comap f) := by
-- proof
  have := hker
  let q := leviComapMap f J
  have _ : LieAlgebra.IsSolvable q.ker :=
    (leviComapMapKerToKer_injective f J).lieAlgebra_isSolvable
  exact levi_isSolvable_of_ker_quotient q (leviComapMap_surjective f hf J)



/--
[leviMapRestrict_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviMapRestrict_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (I : LieIdeal K L) :
-- imply
  Function.Surjective (leviMapRestrict f I) := by
-- proof
  intro y
  obtain ⟨x, hx⟩ := LieIdeal.mem_map_of_surjective hf y.2
  refine ⟨x, ?_⟩
  exact Subtype.ext hx



/--
[levi_isSolvable_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_isSolvable_map
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
-- given
  (f : LieHom K L L') (hf : Function.Surjective f) (I : LieIdeal K L)
  [LieAlgebra.IsSolvable I] :
-- imply
  LieAlgebra.IsSolvable (I.map f) :=
-- proof
  (leviMapRestrict_surjective f hf I).lieAlgebra_isSolvable



/--
[levi_radical_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_radical_quotient
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (I : LieIdeal K L) (hI : I ≤ LieAlgebra.radical K L) :
-- imply
  (LieAlgebra.radical K L).map (leviQuotientMk I) =
    LieAlgebra.radical K (L ⧸ I) := by
-- proof
  let q := leviQuotientMk I
  have hq : Function.Surjective q := leviQuotientMk_surjective I
  apply le_antisymm
  · rw [← LieIdeal.solvable_iff_le_radical]
    exact levi_isSolvable_map q hq (LieAlgebra.radical K L)
  · change LieAlgebra.radical K (L ⧸ I) ≤
    (LieAlgebra.radical K L).map q
    have hmapComap :
      ((LieAlgebra.radical K (L ⧸ I)).comap q).map q =
        LieAlgebra.radical K (L ⧸ I) := by
      rw [LieIdeal.map_comap_eq (q.isIdealMorphism_of_surjective hq)]
      rw [q.idealRange_eq_top_of_surjective hq, top_inf_eq]
    rw [← hmapComap]
    apply LieIdeal.map_mono
    rw [← LieIdeal.solvable_iff_le_radical]
    have hker : q.ker = I := leviQuotientMk_ker I
    have _ : LieAlgebra.IsSolvable q.ker := by
      rw [hker]
      exact LieAlgebra.le_solvable_ideal_solvable hI inferInstance
    exact levi_isSolvable_comap q hq (LieAlgebra.radical K (L ⧸ I))



/--
[levi_radical_quotient_radical_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_radical_quotient_radical_eq_bot
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  LieAlgebra.radical K (L ⧸ LieAlgebra.radical K L) = ⊥ := by
-- proof
  rw [← levi_radical_quotient (LieAlgebra.radical K L) le_rfl]
  rw [LieIdeal.map_eq_bot_iff, leviQuotientMk_ker]



/--
[levi_quotient_radical_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_quotient_radical_isSemisimple
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  LieAlgebra.IsSemisimple K (L ⧸ LieAlgebra.radical K L) := by
-- proof
  let _ : LieAlgebra.HasTrivialRadical K (L ⧸ LieAlgebra.radical K L) :=
    ⟨levi_radical_quotient_radical_eq_bot⟩
  exact inferInstance



/--
[levi_split_central_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_split_central_kernel
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieRing G] [LieAlgebra K G] [Module.Finite K G] [LieAlgebra.IsSemisimple K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q)
  (hcentral : ∀ x ∈ q.ker, ∀ y : L, Bracket.bracket x y = 0) :
-- imply
  ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
    ((q.ker : Submodule K L) + (S : Submodule K L) = ⊤) ∧
    ((q.ker : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
-- proof
  let rangeIncl : q.range →ₗ⁅K⁆ G := q.range.incl
  have hRangeIncl : Function.Bijective rangeIncl := by
    constructor
    · intro x y h
      exact Subtype.ext h
    · intro y
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨⟨q x, LieHom.mem_range_self q x⟩, rfl⟩
  let eRange : q.range ≃ₗ⁅K⁆ G := LieEquiv.ofBijective rangeIncl hRangeIncl
  let eQuot : (L ⧸ q.ker) ≃ₗ⁅K⁆ G := q.quotKerEquivRange.trans eRange
  let _ : LieAlgebra.IsKilling K (L ⧸ q.ker) :=
    LieAlgebra.isKilling_of_equiv eQuot.symm
  let _ : LieAlgebra.IsSemisimple K (L ⧸ q.ker) := inferInstance
  have hkerAction : ∀ x ∈ q.ker, ∀ y : L, ⁅x, y⁆ = 0 := hcentral
  obtain ⟨U, hU⟩ :=
    levi_factor_exists_isCompl q.ker hkerAction (q.ker : LieSubmodule K L L)
  let qU : U →ₗ⁅K⁆ G := q.comp (LieSubalgebra.incl (LieIdeal.toLieSubalgebra K L U))
  have hqUInjective : Function.Injective qU := by
    intro x y hxy
    apply Subtype.ext
    have hdiffKer : x.1 - y.1 ∈ q.ker := by
      rw [LieHom.mem_ker]
      rw [map_sub]
      change qU x - qU y = 0
      rw [hxy, sub_self]
    have hdiffU : x.1 - y.1 ∈ U := U.sub_mem x.2 y.2
    have hdiffBot : x.1 - y.1 ∈ (⊥ : LieSubmodule K L L) := by
      rw [← hU.inf_eq_bot]
      exact ⟨hdiffKer, hdiffU⟩
    have hdiff : x.1 - y.1 = 0 := by simpa using hdiffBot
    exact sub_eq_zero.mp hdiff
  have hqUSurjective : Function.Surjective qU := by
    intro y
    obtain ⟨x, hx⟩ := hq y
    have hxSup : x ∈ q.ker ⊔ U := by
      rw [hU.sup_eq_top]
      trivial
    rw [LieSubmodule.mem_sup] at hxSup
    obtain ⟨z, hz, u, hu, hzu⟩ := hxSup
    refine ⟨⟨u, hu⟩, ?_⟩
    change q u = y
    have hz0 : q z = 0 := LieHom.mem_ker.mp hz
    calc
      q u = q (z + u) := by rw [map_add, hz0, zero_add]
      _ = q x := congrArg q hzu
      _ = y := hx
  let eU : U ≃ₗ⁅K⁆ G := LieEquiv.ofBijective qU ⟨hqUInjective, hqUSurjective⟩
  let _ : LieAlgebra.IsKilling K U := LieAlgebra.isKilling_of_equiv eU.symm
  let _ : LieAlgebra.IsSemisimple K U := inferInstance
  let S := LieIdeal.toLieSubalgebra K L U
  let UtoS : U →ₗ⁅K⁆ S :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      map_lie' := by
        intro x y
        apply Subtype.ext
        rfl }
  have hUtoS : Function.Bijective UtoS := by
    constructor
    · intro x y h
      have h' := congrArg (fun z : S ↦ z.1) h
      change x.1 = y.1 at h'
      exact Subtype.ext h'
    · intro y
      refine ⟨⟨y.1, y.2⟩, ?_⟩
      apply Subtype.ext
      rfl
  let eUS : U ≃ₗ⁅K⁆ S := LieEquiv.ofBijective UtoS hUtoS
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eUS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.sup_eq_top
  · rw [← LieSubmodule.isCompl_toSubmodule] at hU
    exact hU.inf_eq_bot



/--
[levi_abelian_radical_map](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_abelian_radical_map
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let P : LieSubmodule K L V := Bracket.bracket R ⊤
  ∃ f : V, (∀ r : R, f.1 r = r) ∧ (∀ x : L, Bracket.bracket x f ∈ P) := by
-- proof
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let Z := (leviHomVanishing R).comap V.incl
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  have hPZ : P ≤ Z := by
    rw [LieSubmodule.lie_le_iff]
    intro x hx f _
    exact levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x
  let Wbar := Z.map (LieSubmodule.Quotient.mk' P)
  have hRaction : ∀ x ∈ R, ∀ m : V ⧸ P, ⁅x, m⁆ = 0 := by
    intro x hx m
    induction m using Submodule.Quotient.induction_on with
    | _ f =>
      change LieSubmodule.Quotient.mk' P ⁅x, f⁆ = 0
      rw [LieSubmodule.Quotient.mk_eq_zero]
      exact LieSubmodule.lie_mem_lie hx (LieSubmodule.mem_top f)
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨C, hC⟩ := levi_factor_exists_isCompl R hRaction Wbar
  obtain ⟨Q, hQ⟩ := R.toSubmodule.exists_isCompl
  let p : L →ₗ[K] R := R.toSubmodule.projectionOnto Q hQ
  have hp (r : R) : p r = r := Submodule.projectionOnto_apply_left hQ r
  let pv : V := ⟨p, 1, fun r ↦ by rw [hp, one_smul]⟩
  let pvbar : V ⧸ P := LieSubmodule.Quotient.mk' P pv
  have hpvbar : pvbar ∈ Wbar ⊔ C := by
    rw [hC.sup_eq_top]
    trivial
  rw [LieSubmodule.mem_sup] at hpvbar
  obtain ⟨z, hz, c, hc, hzc⟩ := hpvbar
  rw [LieSubmodule.mem_map] at hz
  obtain ⟨z₀, hz₀, hz₀eq⟩ := hz
  let f : V := pv - z₀
  have hfbar : LieSubmodule.Quotient.mk' P f = c := by
    change LieSubmodule.Quotient.mk' P (pv - z₀) = c
    rw [map_sub, hz₀eq]
    change pvbar - z = c
    rw [← hzc]
    abel
  have hfApply (r : R) : f.1 r = r := by
    change (pv.1 - z₀.1) r = r
    rw [LinearMap.sub_apply, hp]
    have hz₀r : z₀.1 r = 0 := hz₀ r
    rw [hz₀r, sub_zero]
  refine ⟨f, hfApply, ?_⟩
  intro x
  have hxcC : ⁅x, c⁆ ∈ C := C.lie_mem hc
  have hxcW : ⁅x, c⁆ ∈ Wbar := by
    rwa [← hfbar, ← LieModuleHom.map_lie]
      (levi_lie_mem_HomVanishing_of_mem_scalarMaps R f x)
  have hxcBot : ⁅x, c⁆ ∈ (⊥ : LieSubmodule K L (V ⧸ P)) := by
    rw [← hC.inf_eq_bot]
    exact ⟨hxcW, hxcC⟩
  have hxcZero : ⁅x, c⁆ = 0 := by simpa using hxcBot
  rw [← LieSubmodule.Quotient.mk_eq_zero]
  rw [LieModuleHom.map_lie, hfbar, hxcZero]



/--
[levi_lie_le_range_theta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_lie_le_range_theta
  [Field K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) (f : leviHomScalarMaps (L := L) I) (hI : IsLieAbelian I)
  (hf : ∀ r : I, f.1 r = r) :
-- imply
  (Bracket.bracket I (⊤ : LieSubmodule K L (leviHomScalarMaps I)) :
      LieSubmodule K L (leviHomScalarMaps I)).toSubmodule ≤
    LinearMap.range (leviTheta I f) := by
-- proof
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span]
  rw [Submodule.span_le]
  rintro g ⟨r, v, rfl⟩
  obtain ⟨a, ha⟩ := v.1.2
  refine ⟨a • r, ?_⟩
  apply Subtype.ext
  ext y
  change
    ((⁅((a • r).1 : L), (f.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L) =
      ((⁅(r.1 : L), (v.1.1 : L →ₗ[K] I)⁆ : L →ₗ[K] I) y : L)
  rw [LieHom.lie_apply, LieHom.lie_apply]
  change
    ⁅(a • r : I).1, (f.1 y).1⁆ - (f.1 ⁅(a • r : I).1, y⁆).1 =
      ⁅r.1, (v.1.1 y).1⁆ - (v.1.1 ⁅r.1, y⁆).1
  have hry : ⁅r.1, y⁆ ∈ I := lie_mem_left K L I r.1 y r.2
  have hary : ⁅(a • r : I).1, y⁆ ∈ I :=
    lie_mem_left K L I (a • r).1 y (a • r).2
  have hrv : ⁅r.1, (v.1.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial r (v.1.1 y))
  have harf : ⁅(a • r : I).1, (f.1 y).1⁆ = 0 :=
    congrArg Subtype.val (hI.trivial (a • r) (f.1 y))
  rw [hrv, harf, zero_sub, zero_sub]
  have hv := congrArg Subtype.val (ha (⟨⁅r.1, y⁆, hry⟩ : I))
  have hfv := congrArg Subtype.val (hf (⟨⁅(a • r : I).1, y⁆, hary⟩ : I))
  rw [hv, hfv]
  simp only [SetLike.val_smul, smul_lie]



/--
[levi_exists_of_abelian_radical](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_exists_of_abelian_radical
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (hR : IsLieAbelian (LieAlgebra.radical K L)) :
-- imply
  ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
    ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
    ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
-- proof
  let R := LieAlgebra.radical K L
  let V := leviHomScalarMaps (L := L) R
  let P : LieSubmodule K L V := ⁅R, ⊤⁆
  obtain ⟨f, hf, hfP⟩ := levi_abelian_radical_map (K := K) (L := L)
  have hPrange : P.toSubmodule ≤ LinearMap.range (leviTheta R f) :=
    levi_lie_le_range_theta R hR f hf
  let H := leviStabilizer R f
  have hRH : (R : Submodule K L) + (H : Submodule K L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxP : ⁅x, f⁆ ∈ P := hfP x
    obtain ⟨r, hr⟩ := hPrange hxP
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r.1, r.2, x - r.1, ?_, ?_⟩
    · change ⁅x - r.1, f⁆ = 0
      rw [sub_lie]
      change ⁅r.1, f⁆ = ⁅x, f⁆ at hr
      rw [hr, sub_self]
    · abel
  let q := leviQuotientMk R
  let qH : H →ₗ⁅K⁆ L ⧸ R := q.comp H.incl
  have hqH : Function.Surjective qH := by
    intro y
    obtain ⟨x, hx⟩ := leviQuotientMk_surjective R y
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    refine ⟨⟨h, hh⟩, ?_⟩
    change q h = y
    have hqr : q r = 0 := by
      rwa [← LieHom.mem_ker, leviQuotientMk_ker]
    calc
      q h = q (r + h) := by rw [map_add, hqr, zero_add]
      _ = q x := congrArg q hrh
      _ = y := hx
  have hcentral : ∀ x ∈ qH.ker, ∀ y : H, ⁅x, y⁆ = 0 := by
    intro x hx y
    have hxq : q x.1 = 0 := by
      exact LieHom.mem_ker.mp hx
    have hxR : x.1 ∈ R := by
      rwa [← leviQuotientMk_ker R, LieHom.mem_ker]
    have hxStab : ⁅x.1, f⁆ = 0 := x.2
    have hmap := congrArg Subtype.val hxStab
    have heval := congrArg (fun g : L →ₗ[K] R ↦ g y.1) hmap
    change ⁅x.1, f.1 y.1⁆ - f.1 ⁅x.1, y.1⁆ = 0 at heval
    have hab : ⁅(⟨x.1, hxR⟩ : R), f.1 y.1⁆ = 0 :=
      hR.trivial ⟨x.1, hxR⟩ (f.1 y.1)
    have hab' : ⁅x.1, f.1 y.1⁆ = 0 := hab
    rw [hab', zero_sub] at heval
    have hfxy : f.1 ⁅x.1, y.1⁆ = 0 := neg_eq_zero.mp heval
    have hxyR : ⁅x.1, y.1⁆ ∈ R := lie_mem_left K L R x.1 y.1 hxR
    have hfix := hf (⟨⁅x.1, y.1⁆, hxyR⟩ : R)
    apply Subtype.ext
    have hzero := congrArg Subtype.val hfxy
    have hfix' := congrArg Subtype.val hfix
    rwa [hfix'] at hzero
  let _ : LieAlgebra.IsSemisimple K (L ⧸ R) :=
    levi_quotient_radical_isSemisimple
  obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
    levi_split_central_kernel qH hqH hcentral
  let S := T.map H.incl
  have hHincl : Function.Injective H.incl := by
    intro x y h
    exact Subtype.ext h
  let eTS : T ≃ₗ⁅K⁆ S := LieSubalgebra.equivMapOfInjective H.incl T hHincl
  let _ : LieAlgebra.IsKilling K T := inferInstance
  let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eTS
  let _ : LieAlgebra.IsSemisimple K S := inferInstance
  refine ⟨S, inferInstance, ?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hxTop : x ∈ (R : Submodule K L) + (H : Submodule K L) := by
      rw [hRH]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxTop
    obtain ⟨r, hr, h, hh, hrh⟩ := hxTop
    have hhTop : (⟨h, hh⟩ : H) ∈
      (qH.ker : Submodule K H) + (T : Submodule K H) := by
      rw [hTsum]
      trivial
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hhTop
    obtain ⟨z, hz, t, ht, hzt⟩ := hhTop
    change x ∈ (R : Submodule K L) + (S : Submodule K L)
    rw [Submodule.add_eq_sup, Submodule.mem_sup]
    refine ⟨r + z.1, R.add_mem hr ?_, t.1, ?_, ?_⟩
    · have hzq : q z.1 = 0 := LieHom.mem_ker.mp hz
      have hzker : z.1 ∈ (leviQuotientMk R).ker := LieHom.mem_ker.mpr hzq
      change z.1 ∈ R
      rwa [leviQuotientMk_ker] at hzker
    · exact (LieSubalgebra.mem_map H.incl T t.1).mpr ⟨t, ht, rfl⟩
    · have hhval : z.1 + t.1 = h := congrArg Subtype.val hzt
      rw [← hrh, ← hhval]
      abel
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨t, ht, htval⟩ := (LieSubalgebra.mem_map H.incl T x).mp hx.2
    have htR : t.1 ∈ R := by
      change H.incl t ∈ R
      rwa [htval]
    have htKer : t ∈ qH.ker := by
      rw [LieHom.mem_ker]
      change q t.1 = 0
      rwa [← LieHom.mem_ker, leviQuotientMk_ker]
    have htBot : t ∈ (⊥ : Submodule K H) := by
      rw [← hTinf]
      exact ⟨htKer, ht⟩
    have htZero : t = 0 := by simpa using htBot
    change x = 0
    rw [← htval, htZero, map_zero]



/--
[leviSubalgebraComapMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviSubalgebraComapMap_surjective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing G] [LieAlgebra K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q) (T : LieSubalgebra K G) :
-- imply
  Function.Surjective (leviSubalgebraComapMap q T) := by
-- proof
  intro y
  obtain ⟨x, hx⟩ := hq y
  have hxT : x ∈ T.comap q := by
    change q x ∈ T
    rwa [hx]
  refine ⟨⟨x, hxT⟩, ?_⟩
  apply Subtype.ext
  exact hx



/--
[leviSubalgebraComapKerToKer_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma leviSubalgebraComapKerToKer_injective
  [CommRing K] [LieRing L] [LieAlgebra K L] [LieRing G] [LieAlgebra K G]
-- given
  (q : LieHom K L G) (T : LieSubalgebra K G) :
-- imply
  Function.Injective (leviSubalgebraComapKerToKer q T) := by
-- proof
  intro x y h
  have hxy := congrArg (fun z : q.ker ↦ z.1) h
  change x.1.1 = y.1.1 at hxy
  exact Subtype.ext (Subtype.ext hxy)



/--
[levi_radical_comap_semisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_radical_comap_semisimple
  [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [LieRing G] [LieAlgebra K G] [Module.Finite K G]
-- given
  (q : LieHom K L G) (hq : Function.Surjective q) (T : LieSubalgebra K G)
  [LieAlgebra.IsSemisimple K T] [LieAlgebra.IsSolvable q.ker] :
-- imply
  LieAlgebra.radical K (T.comap q) = (leviSubalgebraComapMap q T).ker := by
-- proof
  let qT := leviSubalgebraComapMap q T
  have hqT : Function.Surjective qT := leviSubalgebraComapMap_surjective q hq T
  have _ : LieAlgebra.IsSolvable qT.ker :=
    (leviSubalgebraComapKerToKer_injective q T).lieAlgebra_isSolvable
  apply le_antisymm
  · rw [← LieIdeal.map_eq_bot_iff]
    have hsolv : LieAlgebra.IsSolvable ((LieAlgebra.radical K (T.comap q)).map qT) :=
      levi_isSolvable_map qT hqT (LieAlgebra.radical K (T.comap q))
    have hle : (LieAlgebra.radical K (T.comap q)).map qT ≤
      LieAlgebra.radical K T :=
      (LieIdeal.solvable_iff_le_radical (R := K) (L := T) _).mp hsolv
    simpa using hle
  · exact (LieIdeal.solvable_iff_le_radical (R := K) (L := T.comap q) _).mp inferInstance



/--
[levi_derived_radical_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_derived_radical_lt
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
-- given
  (hR : ¬ IsLieAbelian (LieAlgebra.radical K L)) :
-- imply
  Bracket.bracket (LieAlgebra.radical K L) (LieAlgebra.radical K L) <
    LieAlgebra.radical K L := by
-- proof
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  have hRne : R ≠ ⊥ := by
    intro h
    apply hR
    rw [show LieAlgebra.radical K L = ⊥ from h]
    infer_instance
  let _ : Nontrivial R :=
    (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hRne
  have hder : LieAlgebra.derivedSeries K R 1 < ⊤ :=
    LieAlgebra.derivedSeries_lt_top_of_solvable K R
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  refine lt_of_le_of_ne hDle ?_
  intro hEq
  change D = R at hEq
  have htop : LieAlgebra.derivedSeries K R 1 = ⊤ := by
    rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap]
    change D.comap R.incl = ⊤
    rw [hEq]
    exact LieIdeal.comap_incl_self R
  exact hder.ne htop



/--
[levi_quotient_derived_radical_abelian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_quotient_derived_radical_abelian
  [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] :
-- imply
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := Bracket.bracket R R
  IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) := by
-- proof
  dsimp only
  let R := LieAlgebra.radical K L
  let D : LieIdeal K L := ⁅R, R⁆
  let q := leviQuotientMk D
  have hq : Function.Surjective q := leviQuotientMk_surjective D
  have hDle : D ≤ R := LieSubmodule.lie_le_left R R
  have hrad : R.map q = LieAlgebra.radical K (L ⧸ D) :=
    levi_radical_quotient D hDle
  rw [← hrad]
  refine ⟨?_⟩
  intro x y
  obtain ⟨rx, hrx⟩ := LieIdeal.mem_map_of_surjective hq x.2
  obtain ⟨ry, hry⟩ := LieIdeal.mem_map_of_surjective hq y.2
  apply Subtype.ext
  change ⁅x.1, y.1⁆ = 0
  rw [← hrx, ← hry, ← q.map_lie]
  have hbr : ⁅rx.1, ry.1⁆ ∈ D := LieSubmodule.lie_mem_lie rx.2 ry.2
  rwa [← LieHom.mem_ker, leviQuotientMk_ker]



/--
[levi_decomposition_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma levi_decomposition_aux
  (n : ℕ) {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  (hDim : Module.finrank K (LieAlgebra.radical K L) < n) :
  ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple K S ∧
    ((LieAlgebra.radical K L : Submodule K L) + (S : Submodule K L) = ⊤) ∧
    ((LieAlgebra.radical K L : Submodule K L) ⊓ (S : Submodule K L) = ⊥) := by
  induction n generalizing L with
  | zero => omega
  | succ n ih =>
    let R := LieAlgebra.radical K L
    by_cases hRabelian : IsLieAbelian R
    · exact levi_exists_of_abelian_radical hRabelian
    · let D : LieIdeal K L := ⁅R, R⁆
      let q := leviQuotientMk D
      have hq : Function.Surjective q := leviQuotientMk_surjective D
      have hDle : D ≤ R := LieSubmodule.lie_le_left R R
      have hDlt : D < R := levi_derived_radical_lt hRabelian
      have hDfin : Module.finrank K D < Module.finrank K R :=
        Submodule.finrank_lt_finrank_of_lt hDlt
      have hQabelian : IsLieAbelian (LieAlgebra.radical K (L ⧸ D)) :=
        levi_quotient_derived_radical_abelian
      obtain ⟨T, hTsemi, hTsum, hTinf⟩ :=
        levi_exists_of_abelian_radical hQabelian
      let L₁ := T.comap q
      let qT := leviSubalgebraComapMap q T
      have hqT : Function.Surjective qT :=
        leviSubalgebraComapMap_surjective q hq T
      have _ : LieAlgebra.IsSemisimple K T := hTsemi
      have _ : LieAlgebra.IsSolvable q.ker := by
        rw [leviQuotientMk_ker]
        exact LieAlgebra.le_solvable_ideal_solvable hDle inferInstance
      have hRad₁ : LieAlgebra.radical K L₁ = qT.ker :=
        levi_radical_comap_semisimple q hq T
      have hFinKer : Module.finrank K qT.ker ≤ Module.finrank K q.ker :=
        LinearMap.finrank_le_finrank_of_injective
          (leviSubalgebraComapKerToKer_injective q T)
      have hFinRad₁ : Module.finrank K (LieAlgebra.radical K L₁) < n := by
        have hRle : Module.finrank K R ≤ n := Nat.lt_succ_iff.mp hDim
        have hkerD : Module.finrank K q.ker = Module.finrank K D := by
          rw [leviQuotientMk_ker]
        rw [hRad₁]
        calc
          Module.finrank K qT.ker ≤ Module.finrank K q.ker := hFinKer
          _ = Module.finrank K D := hkerD
          _ < Module.finrank K R := hDfin
          _ ≤ n := hRle
      obtain ⟨S₁, hS₁semi, hS₁sum, hS₁inf⟩ := ih hFinRad₁
      let S := S₁.map L₁.incl
      have hL₁incl : Function.Injective L₁.incl := by
        intro x y h
        exact Subtype.ext h
      let eS : S₁ ≃ₗ⁅K⁆ S :=
        LieSubalgebra.equivMapOfInjective L₁.incl S₁ hL₁incl
      let _ : LieAlgebra.IsSemisimple K S₁ := hS₁semi
      let _ : LieAlgebra.IsKilling K S₁ := inferInstance
      let _ : LieAlgebra.IsKilling K S := LieAlgebra.isKilling_of_equiv eS
      let _ : LieAlgebra.IsSemisimple K S := inferInstance
      have hRadQ : R.map q = LieAlgebra.radical K (L ⧸ D) :=
        levi_radical_quotient D hDle
      refine ⟨S, inferInstance, ?_, ?_⟩
      · rw [eq_top_iff]
        intro x _
        have hxQ : q x ∈
          (LieAlgebra.radical K (L ⧸ D) : Submodule K (L ⧸ D)) +
            (T : Submodule K (L ⧸ D)) := by
          rw [hTsum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hxQ
        obtain ⟨a, ha, t, ht, hat⟩ := hxQ
        have haMap : a ∈ R.map q := by
          rwa [hRadQ]
        obtain ⟨r, hr⟩ := LieIdeal.mem_map_of_surjective hq haMap
        have hxt : q (x - r.1) = t := by
          rw [map_sub, hr]
          rw [← hat]
          abel
        let l₁ : L₁ := ⟨x - r.1, by
          change q (x - r.1) ∈ T
          rw [hxt]
          exact ht⟩
        have hl₁Top : l₁ ∈
          (LieAlgebra.radical K L₁ : Submodule K L₁) +
            (S₁ : Submodule K L₁) := by
          rw [hS₁sum]
          trivial
        rw [Submodule.add_eq_sup, Submodule.mem_sup] at hl₁Top
        obtain ⟨z, hz, s, hs, hzs⟩ := hl₁Top
        have hzKer : z ∈ qT.ker := by
          rwa [← hRad₁]
        have hzR : z.1 ∈ R := by
          have hzqT := LieHom.mem_ker.mp hzKer
          have hzq := congrArg Subtype.val hzqT
          change q z.1 = 0 at hzq
          have hzD : z.1 ∈ D := by
            rwa [← leviQuotientMk_ker D, LieHom.mem_ker]
          exact hDle hzD
        change x ∈ (R : Submodule K L) + (S : Submodule K L)
        rw [Submodule.add_eq_sup, Submodule.mem_sup]
        refine ⟨r.1 + z.1, R.add_mem r.2 hzR, s.1, ?_, ?_⟩
        · exact (LieSubalgebra.mem_map L₁.incl S₁ s.1).mpr ⟨s, hs, rfl⟩
        · have hl₁val : z.1 + s.1 = x - r.1 := congrArg Subtype.val hzs
          calc
            r.1 + z.1 + s.1 = r.1 + (z.1 + s.1) := by abel
            _ = r.1 + (x - r.1) := by rw [hl₁val]
            _ = x := by abel
      · rw [eq_bot_iff]
        intro x hx
        obtain ⟨s, hs, hsx⟩ := (LieSubalgebra.mem_map L₁.incl S₁ x).mp hx.2
        have hsR : s.1 ∈ R := by
          have hsval : s.1 = x := hsx
          rwa [hsval]
        have hqsR : q s.1 ∈ LieAlgebra.radical K (L ⧸ D) := by
          rw [← hRadQ]
          exact LieIdeal.mem_map hsR
        have hqsT : q s.1 ∈ T := s.2
        have hqsBot : q s.1 ∈ (⊥ : Submodule K (L ⧸ D)) := by
          rw [← hTinf]
          exact ⟨hqsR, hqsT⟩
        have hqsZero : q s.1 = 0 := by simpa using hqsBot
        have hsKer : s ∈ qT.ker := by
          rw [LieHom.mem_ker]
          apply Subtype.ext
          exact hqsZero
        have hsRad : s ∈ LieAlgebra.radical K L₁ := by
          rwa [hRad₁]
        have hsBot : s ∈ (⊥ : Submodule K L₁) := by
          rw [← hS₁inf]
          exact ⟨hsRad, hs⟩
        have hsZero : s = 0 := by simpa using hsBot
        change x = 0
        rw [← hsx, hsZero, map_zero]



/--
[levi_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
Every finite-dimensional Lie algebra `L` over a field `K` of characteristic zero decomposes as
`K`-vector spaces into its solvable radical `LieAlgebra.radical K L` plus a semisimple Levi factor
`S : LieSubalgebra K L` with sum `⊤` and intersection `⊥`. Source: E. E. Levi, Atti Accad. Sci.
Torino 1905 and A. I. Malcev, Izv. Akad. Nauk SSSR 1945; Bourbaki, Lie I; Lean states K-module
direct sum form over char-zero fields.
Proves `Wanted` entry `levi_decomposition`.
Proof: Weyl's complete reducibility lemma is proved with the trace-form Casimir operator. The
Levi factor is then constructed for an abelian radical and the general case follows by induction
through the derived ideal of the radical.
-/
private lemma levi_decomposition
  {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [Module.Finite K L] :
  ∃ (S : LieSubalgebra K L), LieAlgebra.IsSemisimple K S ∧
    (↑(LieAlgebra.radical K L) + (S : Submodule K L) = (⊤ : Submodule K L)) ∧
    (↑(LieAlgebra.radical K L) ⊓ (S : Submodule K L) = (⊥ : Submodule K L)) := by
  exact levi_decomposition_aux
    (Module.finrank K (LieAlgebra.radical K L) + 1) (Nat.lt_succ_self _)


/--
[levi_scalar_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma scalar_unique
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (a b : K) (hW : W ≠ ⊥)
  (h : ∀ w : W, a • w = b • w) :
-- imply
  a = b := by
-- proof
  apply levi_scalar_unique W hW h

/--
[leviHomScalar_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma homScalar_ker
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  LinearMap.ker (leviHomScalar W hW) =
    (leviHomVanishing W).toSubmodule.comap
      (leviHomScalarMaps W).toSubmodule.subtype := by
-- proof
  apply leviHomScalar_ker W hW

/--
[leviHomScalar_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma homScalar_surjective
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  Function.Surjective (leviHomScalar W hW) := by
-- proof
  apply leviHomScalar_surjective W hW

/--
[leviHomScalarMaps_quotient_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma homScalarMaps_quotient_finrank
  [Field K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]
-- given
  (W : LieSubmodule K L M) (hW : W ≠ ⊥) :
-- imply
  Module.finrank K
    (leviHomScalarMaps W ⧸
      (leviHomVanishing W).comap (leviHomScalarMaps W).incl) = 1 := by
-- proof
  apply leviHomScalarMaps_quotient_finrank W hW

/--
[leviFactorAction_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma factorAction_mk
  [CommRing K] [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M]
-- given
  (I : LieIdeal K L) (hI : ∀ x ∈ I, ∀ m : M, Bracket.bracket x m = 0) (x : L) (m : M) :
-- imply
  leviFactorAction I hI (LieSubmodule.Quotient.mk x) m = Bracket.bracket x m := by
-- proof
  apply leviFactorAction_mk I hI x m

/--
[leviQuotientMk_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma quotientMk_apply
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) (x : L) :
-- imply
  leviQuotientMk I x = LieSubmodule.Quotient.mk x := by
-- proof
  apply leviQuotientMk_apply I x

/--
[leviQuotientMk_ker](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma quotientMk_ker
  [CommRing K] [LieRing L] [LieAlgebra K L]
-- given
  (I : LieIdeal K L) :
-- imply
  (leviQuotientMk I).ker = I := by
-- proof
  apply leviQuotientMk_ker I

/--
[_root_.LieModule.exists_isCompl_of_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/LeviDecomposition.lean)
-/
private lemma LieModule_exists_isCompl_of_isSemisimple_eq
  [Field K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.Finite K L] [LieAlgebra.IsSemisimple K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
  {W : LieSubmodule K L M} :
-- imply
  ∃ U : LieSubmodule K L M, IsCompl W U := by
-- proof
  apply LieModule.exists_isCompl_of_isSemisimple W


-- created on 2026-10-09
-- updated on 2026-10-24

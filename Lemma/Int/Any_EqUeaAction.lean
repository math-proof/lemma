import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.LieGroups.code.MaximalQuotients


/--
[MaximalQuotient.factors_through](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma MaximalQuotient.factors_through
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R}
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
-- given
  (hic : HasInfinitesimalCharacter M χ) :
-- imply
  ∃ (act : MaximalQuotient χ →ₐ[R] Module.End R M), ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M), hic.ueaAction u m = act (MaximalQuotient.proj χ u) m := by
-- proof
  have hideal : maximalQuotientIdeal χ ≤
    TwoSidedIdeal.ker hic.ueaAction.toRingHom := by
    rw [maximalQuotientIdeal, TwoSidedIdeal.span_le]
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    show _ ∈ TwoSidedIdeal.ker hic.ueaAction.toRingHom
    rw [TwoSidedIdeal.mem_ker]
    ext m
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.zero_apply]
    rw [hic.center_acts_by_scalar z m]
    simp [Algebra.algebraMap_eq_smul_one]
  have hker : (maximalQuotientIdeal χ).ringCon ≤
    RingCon.ker hic.ueaAction.toRingHom := by
    intro x y hxy
    rw [RingCon.ker_apply]
    have hmem := (TwoSidedIdeal.rel_iff _ x y).mp hxy
    have h1 : x - y ∈ TwoSidedIdeal.ker hic.ueaAction.toRingHom := hideal hmem
    rw [TwoSidedIdeal.mem_ker] at h1
    have h2 := h1
    simp only [map_sub] at h2
    exact sub_eq_zero.mp h2
  exact ⟨(maximalQuotientIdeal χ).ringCon.liftₐ hic.ueaAction hker,
    fun u _ => by
      show (hic.ueaAction u) _ = ((maximalQuotientIdeal χ).ringCon.liftₐ hic.ueaAction hker ((maximalQuotientIdeal χ).ringCon.mk' u)) _
      simp [RingCon.liftₐ_mk]⟩

/--
[uea_ad_stable_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma uea_ad_stable_mul
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Sa Sb : Submodule R (UniversalEnvelopingAlgebra R 𝔤)}
-- given
  (hSa : ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sa → (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sa)
  (hSb : ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sb → (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sb) :
-- imply
  ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ Sa * Sb → (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ Sa * Sb := by
-- proof
  intro x s hs
  refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun u v hu hv => ?_)
  · have leibniz : UniversalEnvelopingAlgebra.ι R x * (a * b) - a * b * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b +
    a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
    simp only [sub_mul, mul_sub, mul_assoc]; abel
    rw [leibniz]
    exact Submodule.add_mem _
      (Submodule.mul_mem_mul (hSa x a ha) hb)
      (Submodule.mul_mem_mul ha (hSb x b hb))
  · have : UniversalEnvelopingAlgebra.ι R x * (u + v) - (u + v) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) +
    (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) := by
    simp only [mul_add, add_mul]; abel
    rw [this]
    exact Submodule.add_mem _ hu hv

/--
[uea_adjoint_locally_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma uea_adjoint_locally_finite
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Module.Finite R 𝔤] :
-- imply
  ∀ (u : UniversalEnvelopingAlgebra R 𝔤), ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)), Module.Finite R S ∧ u ∈ S ∧ ∀ (x : 𝔤) (s : UniversalEnvelopingAlgebra R 𝔤), s ∈ S → (UniversalEnvelopingAlgebra.ι R x * s - s * UniversalEnvelopingAlgebra.ι R x) ∈ S := by
-- proof
  intro u
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R 𝔤) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    refine ⟨LinearMap.range (Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤)),
      Module.Finite.range _, ?_, fun x s hs => ?_⟩
    · rw [AlgHom.commutes]; exact ⟨r, rfl⟩
    · obtain ⟨r', rfl⟩ := hs
      simp only [Algebra.linearMap_apply]
      rw [Algebra.commutes r' (UniversalEnvelopingAlgebra.ι R x), sub_self]
      exact zero_mem _
  | ι x₀ =>
    refine ⟨Submodule.map (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap ⊤,
      Module.Finite.map _ _, ?_, fun x s hs => ?_⟩
    · exact Submodule.mem_map.mpr ⟨x₀, trivial, rfl⟩
    · obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hs
      simp only [LieHom.coe_toLinearMap]
      have h := (UniversalEnvelopingAlgebra.ι R (L := 𝔤)).map_lie x y
      simp only [LieRing.of_associative_ring_bracket] at h
      rw [h.symm]
      exact Submodule.mem_map.mpr ⟨⁅x, y⁆, trivial, rfl⟩
  | mul a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stable⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stable⟩ := ihb
    refine ⟨Sa * Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).mul (Module.Finite.iff_fg.mp hSb_fin)
    · rw [map_mul]; exact Submodule.mul_mem_mul ha_mem hb_mem
    · exact uea_ad_stable_mul R 𝔤 Sa Sb hSa_stable hSb_stable
  | add a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stable⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stable⟩ := ihb
    refine ⟨Sa ⊔ Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).sup (Module.Finite.iff_fg.mp hSb_fin)
    · rw [map_add]; exact Submodule.mem_sup.mpr ⟨_, ha_mem, _, hb_mem, rfl⟩
    · intro x s hs
      obtain ⟨sa, hsa, sb, hsb, rfl⟩ := Submodule.mem_sup.mp hs
      have : UniversalEnvelopingAlgebra.ι R x * (sa + sb) - (sa + sb) * UniversalEnvelopingAlgebra.ι R x =
        (UniversalEnvelopingAlgebra.ι R x * sa - sa * UniversalEnvelopingAlgebra.ι R x) +
        (UniversalEnvelopingAlgebra.ι R x * sb - sb * UniversalEnvelopingAlgebra.ι R x) := by
        simp only [mul_add, add_mul]; abel
      rw [this]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (hSa_stable x sa hsa))
        (Submodule.mem_sup_right (hSb_stable x sb hsb))

/--
[corollary_14_3_HC](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma corollary_14_3_HC
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤]
  {χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ} :
-- imply
  IsHarishChandraBimodule (MaximalQuotient.bimodule χ) := by
-- proof
  constructor
  intro m
  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _
  obtain ⟨u, hu⟩ := hsurj m
  obtain ⟨S, hS_fin, hu_mem, hS_stable⟩ := uea_adjoint_locally_finite ℂ 𝔤 u
  let projLin : UniversalEnvelopingAlgebra ℂ 𝔤 →ₗ[ℂ] MaximalQuotient χ :=
    (MaximalQuotient.proj χ).toLinearMap
  refine ⟨Submodule.map projLin S, Module.Finite.map S projLin, ?_, ?_⟩
  · exact Submodule.mem_map.mpr ⟨u, hu_mem, hu⟩
  · intro x s' hs'
    obtain ⟨s, hs_mem, rfl⟩ := Submodule.mem_map.mp hs'
    suffices h : projLin (UniversalEnvelopingAlgebra.ι ℂ x * s - s * UniversalEnvelopingAlgebra.ι ℂ x) ∈
      Submodule.map projLin S by
      have had : (MaximalQuotient.bimodule χ).adjointAction x (projLin s) =
        projLin (UniversalEnvelopingAlgebra.ι ℂ x * s - s * UniversalEnvelopingAlgebra.ι ℂ x) := by
        simp only [LieBimodule.adjointAction, MaximalQuotient.bimodule, map_sub]
        rfl
      exact had ▸ h
    exact Submodule.mem_map.mpr ⟨_, hS_stable x s hs_mem, rfl⟩

/--
[algebraic_end_has_eigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma algebraic_end_has_eigenvalue
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Field K]
  [IsAlgClosed K]
  [AddCommGroup V]
  [Module K V]
  {T : Module.End K V}
  {p : Polynomial K}
-- given
  (hp : p ≠ 0)
  (hpT : Polynomial.aeval T p = 0)
  (hV : ∃ v : V, v ≠ 0) :
-- imply
  ∃ (c : K) (v : V), v ≠ 0 ∧ T v = c • v := by
-- proof
  have hdeg : p.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h] at hpT
    simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at hpT
    obtain ⟨m, hm⟩ := hV
    apply hp
    rw [Polynomial.eq_C_of_natDegree_eq_zero h]
    suffices p.coeff 0 = 0 by simp [this]
    by_contra hc
    apply hm
    have h1 : (p.coeff 0 • (1 : Module.End K V)) m = (0 : Module.End K V) m := by rw [hpT]
    simp at h1
    exact h1.resolve_left hc
  have hpdeg' : p.degree ≠ 0 := by intro h'; apply hdeg; simp [Polynomial.natDegree, h']
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hpdeg'
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
  have hcomp : (Polynomial.aeval T (Polynomial.X - Polynomial.C r)) *
    (Polynomial.aeval T q) = 0 := by
    rw [← map_mul, ← hq, hpT]
  by_cases hqT : Polynomial.aeval T q = 0
  · have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hp hq
    exact algebraic_end_has_eigenvalue T q hq_ne hqT hV
  ·
    have : ¬∀ x, Polynomial.aeval T q x = 0 := by
      intro h; apply hqT; ext; exact h _
    push Not at this
    obtain ⟨w, hw⟩ := this
    refine ⟨r, Polynomial.aeval T q w, hw, ?_⟩
    have hzero : Polynomial.aeval T (Polynomial.X - Polynomial.C r)
      (Polynomial.aeval T q w) = 0 := by
      change (Polynomial.aeval T (Polynomial.X - Polynomial.C r) *
        Polynomial.aeval T q) w = 0
      rw [hcomp]; simp
    simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, LinearMap.sub_apply, LinearMap.smul_apply] at hzero
    simp at hzero
    exact sub_eq_zero.mp hzero
termination_by p.natDegree
decreasing_by
  rw [hq]
  have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hp hq
  rw [Polynomial.natDegree_mul (by simp [Polynomial.X_sub_C_ne_zero]) hq_ne,
    Polynomial.natDegree_X_sub_C]
  omega

/--
[isIrreducible_of_isAtom_lieSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma isIrreducible_of_isAtom_lieSubmodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieRing 𝔤']
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤' V]
  {N : LieSubmodule ℂ 𝔤' V}
-- given
  (hN : IsAtom N) :
-- imply
  LieModule.IsIrreducible ℂ 𝔤' ↥N := by
-- proof
  have hNne : N ≠ ⊥ := hN.1
  haveI : Nontrivial ↥N := by
    rw [LieSubmodule.nontrivial_iff_ne_bot]; exact hNne
  apply LieModule.IsIrreducible.mk
  intro P hP
  have h1 : P.map N.incl ≤ N := LieSubmodule.map_incl_le
  have h2 : P.map N.incl ≠ ⊥ := by
    intro heq; apply hP; rw [eq_bot_iff]
    intro x hx
    have hmem : N.incl x ∈ P.map N.incl := LieSubmodule.mem_map_of_mem hx
    rw [heq] at hmem; simp [LieSubmodule.mem_bot] at hmem; simp [hmem]
  have h3 : P.map N.incl = N := (hN.le_iff.mp h1).resolve_left h2
  by_contra h
  have hlt : P < ⊤ := lt_top_iff_ne_top.mpr h
  rw [← LieSubmodule.map_incl_lt_iff_lt_top] at hlt
  exact absurd h3 (ne_of_lt hlt)
universe u_bimod_carrier

/--
[weyl_irred_submodule_of_ad_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma weyl_irred_submodule_of_ad_stable
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  {M : LieBimodule.{_, _, u_bimod_carrier} ℂ 𝔤}
  {S : Submodule ℂ M.carrier}
-- given
  (hS_fin : Module.Finite ℂ S)
  (hS_ne : ∃ (s : M.carrier), s ∈ S ∧ s ≠ 0)
  (hS_stable : ∀ (x : 𝔤) (s : M.carrier), s ∈ S → M.adjointAction x s ∈ S) :
-- imply
  ∃ (V : Type u_bimod_carrier) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V) (_ : Module.Finite ℂ V) (_ : LieModule.IsIrreducible ℂ 𝔤 V) (ι : V →ₗ[ℂ] M.carrier), Function.Injective ι ∧ (∀ (x : 𝔤) (v : V), ι (⁅x, v⁆) = M.adjointAction x (ι v)) := by
-- proof
  letI : LieRingModule 𝔤 M.carrier := M.toLieRingModule'
  letI : LieModule ℂ 𝔤 M.carrier := M.toLieModule'
  let S_lie : LieSubmodule ℂ 𝔤 M.carrier :=
    { toSubmodule := S
      lie_mem := fun {x} {m} hm => hS_stable x m hm }
  haveI : Module.Finite ℂ S_lie := hS_fin
  haveI : IsArtinian ℂ S_lie := inferInstance
  haveI : IsAtomic (LieSubmodule ℂ 𝔤 S_lie) := inferInstance
  have hS_ne_bot : S_lie ≠ ⊥ := by
    obtain ⟨s, hs_mem, hs_ne⟩ := hS_ne
    intro h
    have : s ∈ (⊥ : LieSubmodule ℂ 𝔤 M.carrier) := h ▸ hs_mem
    simp [LieSubmodule.mem_bot] at this
    exact hs_ne this
  haveI : Nontrivial S_lie := by
    rw [LieSubmodule.nontrivial_iff_ne_bot]; exact hS_ne_bot
  have htop_ne_bot : (⊤ : LieSubmodule ℂ 𝔤 S_lie) ≠ ⊥ :=
    top_ne_bot
  obtain ⟨A, hA_atom, _hA_le⟩ :=
    (IsAtomic.eq_bot_or_exists_atom_le (⊤ : LieSubmodule ℂ 𝔤 S_lie)).resolve_left htop_ne_bot
  have hA_irred : LieModule.IsIrreducible ℂ 𝔤 A :=
    isIrreducible_of_isAtom_lieSubmodule A hA_atom
  haveI : Module.Finite ℂ A := inferInstance
  let ι_comp : A →ₗ[ℂ] M.carrier := S_lie.incl.toLinearMap.comp A.incl.toLinearMap
  have hι_inj : Function.Injective ι_comp := by
    intro x y h
    have h1 : S_lie.incl (A.incl x) = S_lie.incl (A.incl y) := h
    have h2 : A.incl x = A.incl y := S_lie.injective_incl h1
    exact A.injective_incl h2
  have hι_lie : ∀ (x : 𝔤) (v : ↥A), ι_comp (⁅x, v⁆) = M.adjointAction x (ι_comp v) := by
    intro x v
    rfl
  exact ⟨↥A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hA_irred, ι_comp, hι_inj, hι_lie⟩

/--
[adjoint_irred_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma adjoint_irred_submodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  {M : LieBimodule.{_, _, u_bimod_carrier} ℂ 𝔤}
-- given
  (hirr : M.IsIrreducible)
  (hlocfin : IsHarishChandraBimodule M) :
-- imply
  ∃ (V : Type u_bimod_carrier) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V) (_ : Module.Finite ℂ V) (_ : LieModule.IsIrreducible ℂ 𝔤 V) (ι : V →ₗ[ℂ] M.carrier), Function.Injective ι ∧ (∀ (x : 𝔤) (v : V), ι (⁅x, v⁆) = M.adjointAction x (ι v)) := by
-- proof
  obtain ⟨m, hm⟩ := hirr.1
  obtain ⟨S, hS_fin, hm_mem, hS_stable⟩ := hlocfin.locally_finite m
  exact weyl_irred_submodule_of_ad_stable M S hS_fin ⟨m, hm_mem, hm⟩ hS_stable

/--
[canonical_element_image_is_subbimodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma canonical_element_image_is_subbimodule
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  {M : LieBimodule ℂ 𝔤}
  {χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ}
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [Module.Finite ℂ V]
  {_ι : V →ₗ[ℂ] M.carrier}
  {ξ : TensorProduct ℂ V (MaximalQuotient χ) →ₗ[ℂ] M.carrier}
-- given
  (_hχ : ∀ (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) (m : M.carrier), M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra ℂ 𝔤)) m = χ z • m)
  (_hι : Function.Injective _ι)
  (_hξ_ne : ξ ≠ 0)
  (hξ_left : ∀ (u : UniversalEnvelopingAlgebra ℂ 𝔤) (t : TensorProduct ℂ V (MaximalQuotient χ)), ξ ((tensorBimodule (LieBimodule.trivial V) χ).leftAction u t) = M.leftAction u (ξ t))
  (hξ_right : ∀ (u : (UniversalEnvelopingAlgebra ℂ 𝔤)ᵐᵒᵖ) (t : TensorProduct ℂ V (MaximalQuotient χ)), ξ ((tensorBimodule (LieBimodule.trivial V) χ).rightAction u t) = M.rightAction u (ξ t)) :
-- imply
  M.IsSubBimodule (LinearMap.range ξ) := by
-- proof
  constructor
  ·
    intro u s hs
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hs
    rw [← hξ_left u t]
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩
  ·
    intro u s hs
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hs
    rw [← hξ_right u t]
    exact LinearMap.mem_range.mpr ⟨_, rfl⟩

/--
[hc_hom_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma hc_hom_finite
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  {N : LieBimodule ℂ 𝔤}
  {W : Type 0}
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  [Module.Finite ℂ W]
-- given
  (hN : IsAdmissibleBimodule N)
  (hirr : LieModule.IsIrreducible ℂ 𝔤 W) :
-- imply
  Module.Finite ℂ (HomAdEquivariant W N) :=
-- proof
  hN.admissible W

/--
[UniversalEnvelopingAlgebra.lift_centralizes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/MaximalQuotients.lean)
-/
@[path]
private lemma lift_centralizes_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [Ring A]
  [Algebra R A]
  {f : 𝔤 →ₗ⁅R⁆ A}
  {E : A}
-- given
  (hf : ∀ x, f x * E = E * f x) :
-- imply
  ∀ u, UniversalEnvelopingAlgebra.lift R f u * E = E * UniversalEnvelopingAlgebra.lift R f u := by
-- proof
  apply UniversalEnvelopingAlgebra.lift_centralizes R 𝔤 f E hf


-- created on 2026-10-23
-- updated on 2026-10-26

import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
open scoped TensorProduct


/--
[TriangularDecomposition.projectToH_of_mem_h](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma TriangularDecomposition.projectToH_of_mem_h
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
-- given
  (h : Δ.𝔥) :
-- imply
  Δ.projectToH (h : 𝔤) = h := by
-- proof
  unfold TriangularDecomposition.projectToH
  set n_neg := (Δ.decomp_exists (h : 𝔤)).choose
  set h₀ := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose
  set n_pos := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose_spec.choose
  have hdecomp := (Δ.decomp_exists (h : 𝔤)).choose_spec.choose_spec.choose_spec
  have heq : (n_neg : 𝔤) + (h₀ : 𝔤) + (n_pos : 𝔤) =
    (0 : Δ.𝔫_neg) + (h : 𝔤) + (0 : Δ.𝔫_pos) := by
    rw [← hdecomp]
    simp [ZeroMemClass.coe_zero, zero_add, add_zero]
  exact (Δ.decomp_unique n_neg 0 h₀ h n_pos 0 heq).2.1

/--
[chevalley_restriction_bijective_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma chevalley_restriction_bijective_aux
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {crd : ChevalleyRestrictionData Δ wg} :
-- imply
  Function.Bijective crd.restrictionMap :=
-- proof
  ⟨chevalley_restriction_injective_aux crd, chevalley_restriction_surjective_aux crd⟩

/--
[chevalley_restriction_lands_in_W_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma chevalley_restriction_lands_in_W_invariants
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {f : (chevalleyRestrictionData wg).S𝔤}
-- given
  (hf : f ∈ (chevalleyRestrictionData wg).adInvariant) :
-- imply
  ((chevalleyRestrictionData wg).restrictionAlgHom f) ∈ (wg.invariantSubalgebra : Set (UniversalEnvelopingAlgebra R Δ.𝔥)) :=
-- proof
  chevalley_restriction_lands_in_W_invariants_aux (chevalleyRestrictionData wg) f hf

/--
[isComplexReflection_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma isComplexReflection_inv
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {g : V ≃ₗ[k] V}
-- given
  (h : IsComplexReflection g) :
-- imply
  IsComplexReflection g.symm where rank_eq_one := by
-- proof
  have key : -(g.symm.toLinearMap - LinearMap.id) =
    g.symm.toLinearMap.comp (g.toLinearMap - LinearMap.id) := by
    ext v; simp [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply, map_sub]
  have hrange : (g.symm.toLinearMap - LinearMap.id).range =
    (g.toLinearMap - LinearMap.id).range.map g.symm.toLinearMap := by
    rw [← LinearMap.range_neg, key, LinearMap.range_comp]
  rw [hrange, LinearEquiv.finrank_map_eq]; exact h.rank_eq_one
  ne_id := by
    intro h_eq; apply h.ne_id; ext v
    have : g.symm (g v) = v := g.symm_apply_apply v
    rw [h_eq] at this; simpa using this

/--
[isComplexReflectionGroup_of_closure_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma isComplexReflectionGroup_of_closure_eq_top
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Group G]
  [Fintype G]
  {ρ : G →* V ≃ₗ[k] V}
-- given
  (hclosure : Subgroup.closure { g : G | IsComplexReflection (ρ g) } = ⊤) :
-- imply
  IsComplexReflectionGroup G ρ where generated_by_reflections g := by
-- proof
  have hg : g ∈ Subgroup.closure { g : G | IsComplexReflection (ρ g) } := by
    rw [hclosure]; exact Subgroup.mem_top g
  suffices key : ∃ (l : List G), (∀ x ∈ l, IsComplexReflection (ρ x)) ∧ g = l.prod by
    obtain ⟨l, hl, rfl⟩ := key
    refine ⟨l.length, fun i => l.get i, fun i => hl _ (l.get_mem i), ?_⟩
    rw [List.ofFn_get]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨[x], by simpa, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨lx, hlx, rfl⟩ := ihx
    obtain ⟨ly, hly, rfl⟩ := ihy
    exact ⟨lx ++ ly, fun a ha => by
      simp only [List.mem_append] at ha; exact ha.elim (hlx a) (hly a),
      by rw [List.prod_append]⟩
  | inv x _ ihx =>
    obtain ⟨lx, hlx, hprod⟩ := ihx
    refine ⟨(lx.map (·⁻¹)).reverse, fun a ha => ?_, ?_⟩
    · simp only [List.mem_reverse, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      show IsComplexReflection (ρ b⁻¹)
      rw [show ρ b⁻¹ = (ρ b).symm from by rw [map_inv]; rfl]
      exact isComplexReflection_inv _ (hlx b hb)
    · rw [hprod, List.prod_inv_reverse]

/--
[isInducedPolynomialAction_deg_pres](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma isInducedPolynomialAction_deg_pres
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Group G]
  [Fintype ι]
  [DecidableEq ι]
  {b : Module.Basis ι k V}
  {ρ : G →* V ≃ₗ[k] V}
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {g : G}
  {p : MvPolynomial ι k}
-- given
  (hcompat : IsInducedPolynomialAction b G ρ algAct) :
-- imply
  ((algAct g) p).totalDegree ≤ p.totalDegree := by
-- proof
  have hX_deg : ∀ i : ι,
    ((algAct g : MvPolynomial ι k →ₐ[k] MvPolynomial ι k) (MvPolynomial.X i)).totalDegree ≤ 1 := by
    intro i
    change ((algAct g) (MvPolynomial.X i)).totalDegree ≤ 1
    rw [hcompat g i]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
    refine Finset.sup_le (fun j _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C]
    simp only [zero_add]
    exact le_of_eq (MvPolynomial.totalDegree_X j)
  let φ : MvPolynomial ι k →ₐ[k] MvPolynomial ι k := (algAct g).toAlgHom
  suffices (φ p).totalDegree ≤ p.totalDegree by exact this
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le (fun v hv => ?_)
  rw [MvPolynomial.monomial_eq, map_mul]
  have hC : φ (MvPolynomial.C (MvPolynomial.coeff v p)) =
    MvPolynomial.C (MvPolynomial.coeff v p) := by
    show (algAct g).toAlgHom (MvPolynomial.C (MvPolynomial.coeff v p)) =
      MvPolynomial.C (MvPolynomial.coeff v p)
    rw [MvPolynomial.algHom_C]; rfl
  rw [hC]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  rw [Finsupp.prod, map_prod]
  simp_rw [map_pow]
  calc (∏ x ∈ v.support, φ (MvPolynomial.X x) ^ v x).totalDegree
    ≤ ∑ x ∈ v.support, (φ (MvPolynomial.X x) ^ v x).totalDegree :=
      MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ x ∈ v.support, v x * (φ (MvPolynomial.X x)).totalDegree :=
      Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ x ∈ v.support, v x * 1 :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (hX_deg i))
    _ = v.sum (fun _ e => e) := by simp [mul_one, Finsupp.sum]
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv

/--
[orbitPoly_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma orbitPoly_monic
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [Group G]
  [Fintype G]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k} :
-- imply
  (orbitPoly algAct p).Monic :=
-- proof
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

/--
[orbitPoly_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma orbitPoly_eval
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [Group G]
  [Fintype G]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k} :
-- imply
  (orbitPoly algAct p).eval p = 0 := by
-- proof
  simp only [orbitPoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_one]

/--
[orbitPoly_map_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma orbitPoly_map_invariant
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [Group G]
  [Fintype G]
  [DecidableEq G]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k}
-- given
  (h : G) :
-- imply
  (orbitPoly algAct p).map (algAct h).toAlgHom.toRingHom = orbitPoly algAct p := by
-- proof
  simp only [orbitPoly]
  rw [Polynomial.map_prod]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  conv_lhs =>
    arg 2
    ext g
    rw [show (algAct h).toAlgHom.toRingHom ((algAct g) p) = (algAct (h * g)) p from by
      simp [map_mul]]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _
    (fun g => by simp [Equiv.mulLeft])

/--
[orbitPoly_coeff_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma orbitPoly_coeff_mem
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [Group G]
  [Fintype G]
  [DecidableEq G]
  [Fintype ι]
  [DecidableEq ι]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k}
  {n : ℕ} :
-- imply
  (orbitPoly algAct p).coeff n ∈ polynomialInvariantSubalgebra k G ι algAct := by
-- proof
  show ∀ g : G, (algAct g) ((orbitPoly algAct p).coeff n) = (orbitPoly algAct p).coeff n
  intro g
  have hmapinv := orbitPoly_map_invariant algAct p g
  have := congr_arg (fun q => Polynomial.coeff q n) hmapinv
  simp only [Polynomial.coeff_map] at this
  exact this

/--
[orbitPoly_coeffs_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma orbitPoly_coeffs_subset
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [Group G]
  [Fintype G]
  [DecidableEq G]
  [Fintype ι]
  [DecidableEq ι]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k} :
-- imply
  (↑(orbitPoly algAct p).coeffs : Set (MvPolynomial ι k)) ⊆ (polynomialInvariantSubalgebra k G ι algAct).toSubring := by
-- proof
  intro c hc
  obtain ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
  exact hn ▸ orbitPoly_coeff_mem algAct p n

/--
[isIntegral_over_invariantSubalgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma isIntegral_over_invariantSubalgebra
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [CharZero k]
  [Group G]
  [Fintype G]
  [DecidableEq G]
  [Fintype ι]
  [DecidableEq ι]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {p : MvPolynomial ι k} :
-- imply
  IsIntegral (polynomialInvariantSubalgebra k G ι algAct) p := by
-- proof
  let S := polynomialInvariantSubalgebra k G ι algAct
  let q := orbitPoly algAct p
  let q' := q.toSubring S.toSubring (orbitPoly_coeffs_subset algAct p)
  have hq'_monic : q'.Monic := by
    rw [Polynomial.monic_toSubring]
    exact orbitPoly_monic algAct p
  have hq'_eval : Polynomial.eval₂ (Subring.subtype S.toSubring) p q' = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_toSubring]
    exact orbitPoly_eval algAct p
  refine ⟨q', hq'_monic, ?_⟩
  rw [show algebraMap ↥S (MvPolynomial ι k) = S.toSubring.subtype from
    (S.toSubring_subtype).symm]
  exact hq'_eval

/--
[remark_11_5_generators_eq_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma remark_11_5_generators_eq_dim
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [CharZero k]
  [IsAlgClosed k]
  {G : Type*}
  [Group G]
  [Fintype G]
  [Fintype ι]
  [DecidableEq ι]
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {r : ℕ}
  {f : Fin r → MvPolynomial ι k}
-- given
  (_hf_inv : ∀ i, f i ∈ polynomialInvariantSubalgebra k G ι algAct)
  (hf_alg : AlgebraicIndependent k f)
  (hf_gen : polynomialInvariantSubalgebra k G ι algAct = Algebra.adjoin k (Set.range f)) :
-- imply
  r = Fintype.card ι := by
-- proof
  classical
  have h_int_inv : ∀ x : MvPolynomial ι k,
    IsIntegral (↥(polynomialInvariantSubalgebra k G ι algAct)) x :=
    fun x => isIntegral_over_invariantSubalgebra algAct x
  have h_int_S : ∀ x : MvPolynomial ι k,
    IsIntegral (↥(Algebra.adjoin k (Set.range f))) x := by
    intro x; have := h_int_inv x; rwa [hf_gen] at this
  have h_isAlgebraic : Algebra.IsAlgebraic (↥(Algebra.adjoin k (Set.range f)))
    (MvPolynomial ι k) := (⟨h_int_S⟩ : Algebra.IsIntegral _ _).isAlgebraic
  have hf_basis : IsTranscendenceBasis k f :=
    hf_alg.isTranscendenceBasis_iff_isAlgebraic.mpr h_isAlgebraic
  have hX_basis : IsTranscendenceBasis k (MvPolynomial.X : ι → MvPolynomial ι k) :=
    IsTranscendenceBasis.mvPolynomial ι k
  have h_eq := hf_basis.lift_cardinalMk_eq hX_basis
  rw [Cardinal.mk_fin, Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_natCast] at h_eq
  exact_mod_cast h_eq

/--
[reflection_subgroup_is_reflection_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma reflection_subgroup_is_reflection_group
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [AddCommGroup V]
  [Module k V]
  [Group G]
  [Fintype G]
  {ρ : G →* V ≃ₗ[k] V}
  {H : Subgroup G}
  [Fintype H]
-- given
  (hH : H = Subgroup.closure { g : G | IsComplexReflection (ρ g) }) :
-- imply
  IsComplexReflectionGroup H (ρ.comp H.subtype) := by
-- proof
  apply isComplexReflectionGroup_of_closure_eq_top (ρ.comp H.subtype)
  have hset : {h : H | IsComplexReflection ((ρ.comp H.subtype) h)} =
    H.subtype ⁻¹' {g : G | IsComplexReflection (ρ g)} := by
    ext ⟨g, _⟩; simp [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [hset, hH]
  exact Subgroup.closure_preimage_eq_top _

/--
[isInducedPolynomialAction_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma isInducedPolynomialAction_restrict
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [CommRing k]
  [AddCommGroup V]
  [Module k V]
  [Fintype ι]
  [DecidableEq ι]
  {b : Module.Basis ι k V}
  [Group G]
  {ρ : G →* V ≃ₗ[k] V}
  {algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)}
  {H : Subgroup G}
-- given
  (hcompat : IsInducedPolynomialAction b G ρ algAct) :
-- imply
  IsInducedPolynomialAction b H (ρ.comp H.subtype) (algAct.comp H.subtype) := by
-- proof
  intro ⟨g, _⟩ i; exact hcompat g i

/--
[ChevalleyRestrictionPolyData.Res_preserves_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma ChevalleyRestrictionPolyData.Res_preserves_degree
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
  {p : MvPolynomial (Fin n) R}
  {d : ℕ}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
  (hp : p.IsHomogeneous d) :
-- imply
  (cpd.Res p).IsHomogeneous d := by
-- proof
  rw [cpd.Res_eq_aeval]
  have h := hp.aeval cpd.Res_components cpd.Res_components_homogeneous
  rwa [one_mul] at h

/--
[ChevalleyRestrictionPolyData.Res_maps_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma ChevalleyRestrictionPolyData.Res_maps_invariants
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
  {p : MvPolynomial (Fin n) R}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
  (hp : p ∈ Subalgebra.invariants cpd.G cpd.G_action) :
-- imply
  (cpd.Res p) ∈ Subalgebra.invariants wg.W cpd.W_action := by
-- proof
  intro w
  obtain ⟨g, hg⟩ := cpd.Res_action_compat w
  rw [← hg p, hp g]

/--
[invariant_vanishes_on_semisimple_locus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma invariant_vanishes_on_semisimple_locus
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
  {S : Set (Fin n → R)}
  {p : MvPolynomial (Fin n) R}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m)
  (hconj : ∀ v ∈ S, ∀ p : MvPolynomial (Fin n) R, p ∈ Subalgebra.invariants cpd.G cpd.G_action → ∃ (h : Fin m → R), MvPolynomial.eval v p = MvPolynomial.eval h (cpd.Res p))
  (hp : p ∈ Subalgebra.invariants cpd.G cpd.G_action)
  (hker : cpd.Res p = 0) :
-- imply
  ∀ v ∈ S, MvPolynomial.eval v p = 0 := by
-- proof
  intro v hv
  obtain ⟨h, heq⟩ := hconj v hv p hp
  rw [heq, hker, map_zero]

/--
[chevalley_res_kernel_trivial_on_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma chevalley_res_kernel_trivial_on_invariants
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [CommRing k]
  {n m : ℕ}
  {G : Type*}
  [Group G]
  {G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k)}
  {Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k}
  {p : MvPolynomial (Fin n) k}
-- given
  (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k), q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
  (hp_inv : p ∈ Subalgebra.invariants G G_action)
  (hp_ker : Res p = 0) :
-- imply
  p = 0 :=
-- proof
  hRes_kernel_trivial p hp_inv hp_ker

/--
[chevalley_restriction_graded_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
lemma chevalley_restriction_graded_isomorphism
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
-- imply
  (Function.Bijective cpd.restrictionMapPoly) ∧ (∀ (p : MvPolynomial (Fin n) R) (d : ℕ), p.IsHomogeneous d → (cpd.Res p).IsHomogeneous d) :=
-- proof
  ⟨chevalley_restriction_polynomial cpd, cpd.Res_preserves_degree⟩

/--
[chevalley_restriction_lands_in_W_invariants_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_lands_in_W_invariants_aux_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {crd : ChevalleyRestrictionData Δ wg}
  {f : crd.S𝔤}
-- given
  (hf : f ∈ crd.adInvariant) :
-- imply
  (crd.restrictionAlgHom f) ∈ (wg.invariantSubalgebra : Set (UniversalEnvelopingAlgebra R Δ.𝔥)) := by
-- proof
  apply chevalley_restriction_lands_in_W_invariants_aux R 𝔤 crd f hf

/--
[chevalley_restriction_injective_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_injective_aux_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {crd : ChevalleyRestrictionData Δ wg} :
-- imply
  Function.Injective crd.restrictionMap := by
-- proof
  apply chevalley_restriction_injective_aux R 𝔤 crd

/--
[chevalley_restriction_surjective_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_surjective_aux_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {crd : ChevalleyRestrictionData Δ wg} :
-- imply
  Function.Surjective crd.restrictionMap := by
-- proof
  apply chevalley_restriction_surjective_aux R 𝔤 crd

/--
[chevalley_restriction_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_injective_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ} :
-- imply
  Function.Injective (chevalleyRestrictionData wg).restrictionMap := by
-- proof
  apply chevalley_restriction_injective R 𝔤

/--
[chevalley_restriction_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_surjective_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ} :
-- imply
  Function.Surjective (chevalleyRestrictionData wg).restrictionMap := by
-- proof
  apply chevalley_restriction_surjective R 𝔤

/--
[chevalley_restriction_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_bijective_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ} :
-- imply
  Function.Bijective (chevalleyRestrictionData wg).restrictionMap := by
-- proof
  apply chevalley_restriction_bijective R 𝔤

/--
[chevalley_restriction_polynomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_polynomial_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  {Δ : TriangularDecomposition R 𝔤}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := R) (𝔤 := 𝔤) wg n m) :
-- imply
  Function.Bijective cpd.restrictionMapPoly := by
-- proof
  apply chevalley_restriction_polynomial R 𝔤 cpd

/--
[chevalley_res_injective_on_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_res_injective_on_invariants_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [CommRing k]
  {n m : ℕ}
  {G : Type*}
  [Group G]
  {G_action : G →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k)}
  {Res : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k}
  {p₁ p₂ : MvPolynomial (Fin n) k}
-- given
  (hRes_kernel_trivial : ∀ (q : MvPolynomial (Fin n) k), q ∈ Subalgebra.invariants G G_action → Res q = 0 → q = 0)
  (hp₁ : p₁ ∈ Subalgebra.invariants G G_action)
  (hp₂ : p₂ ∈ Subalgebra.invariants G G_action)
  (h : Res p₁ = Res p₂) :
-- imply
  p₁ = p₂ := by
-- proof
  apply chevalley_res_injective_on_invariants R 𝔤 G G_action Res hRes_kernel_trivial p₁ p₂ hp₁ hp₂ h

/--
[chevalley_res_surjective_on_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_res_surjective_on_invariants_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [LieRing 𝔤₀]
  [LieAlgebra k 𝔤₀]
  [LieAlgebra.IsKilling k 𝔤₀]
  [FiniteDimensional k 𝔤₀]
  {Δ : TriangularDecomposition k 𝔤₀}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
  {q : MvPolynomial (Fin m) k}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m)
  (hq : q ∈ Subalgebra.invariants wg.W cpd.W_action) :
-- imply
  ∃ p : MvPolynomial (Fin n) k, p ∈ Subalgebra.invariants cpd.G cpd.G_action ∧ cpd.Res p = q := by
-- proof
  apply chevalley_res_surjective_on_invariants R 𝔤 cpd q hq

/--
[chevalley_restriction_theorem_10_1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ChevalleyRestriction.lean)
-/
@[path]
private lemma chevalley_restriction_theorem_10_1_eq
  {R : Type*}
  [Field R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  [LieAlgebra.IsKilling R 𝔤]
  [FiniteDimensional R 𝔤]
  {R 𝔤}
  [Field k]
  [LieRing 𝔤₀]
  [LieAlgebra k 𝔤₀]
  [LieAlgebra.IsKilling k 𝔤₀]
  [FiniteDimensional k 𝔤₀]
  {Δ : TriangularDecomposition k 𝔤₀}
  {wg : WeylGroupData Δ}
  {n m : ℕ}
-- given
  (cpd : ChevalleyRestrictionPolyData (R := k) (𝔤 := 𝔤₀) wg n m) :
-- imply
  Function.Bijective ((cpd.Res.comp (Subalgebra.invariants cpd.G cpd.G_action).val).codRestrict (Subalgebra.invariants wg.W cpd.W_action) (fun ⟨x, hx⟩ => cpd.Res_maps_invariants x hx)) := by
-- proof
  apply chevalley_restriction_theorem_10_1 R 𝔤 cpd


-- created on 2026-10-23

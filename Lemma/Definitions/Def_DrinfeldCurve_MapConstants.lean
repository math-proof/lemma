import Lemma.Definitions.Def_DrinfeldCurve_FunctionField
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace DrinfeldCurve

section Square

variable (q : ℕ) (k k' : Type) [Field k] [Field k'] [Algebra k k']

theorem map_drinfeldPoly : MvPolynomial.map (algebraMap k k') (drinfeldPoly q k) = drinfeldPoly q k' := by
  simp [drinfeldPoly]

namespace CoordRing

def mapConstants : CoordRing q k →+* CoordRing q k' :=
  Ideal.Quotient.lift (drinfeldIdeal q k) ((mk q k').toRingHom.comp (MvPolynomial.map (algebraMap k k')))
    (by
      intro a ha
      rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
      obtain ⟨b, rfl⟩ := ha
      have hmem : MvPolynomial.map (algebraMap k k') (b * (drinfeldPoly q k - 1)) ∈ drinfeldIdeal q k' := by
        rw [map_mul, map_sub, map_one, map_drinfeldPoly, drinfeldIdeal]
        exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
      show mk q k' (MvPolynomial.map (algebraMap k k') (b * (drinfeldPoly q k - 1))) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

theorem mapConstants_mk (f : MvPolynomial (Fin 2) k) :
    mapConstants q k k' (mk q k f) = mk q k' (MvPolynomial.map (algebraMap k k') f) :=
  rfl

theorem mapConstants_x : mapConstants q k k' (x q k) = x q k' := by
  rw [x, mapConstants_mk, MvPolynomial.map_X, x]

theorem mapConstants_y : mapConstants q k k' (y q k) = y q k' := by
  rw [y, mapConstants_mk, MvPolynomial.map_X, y]

theorem mapConstants_algebraMap (c : k) :
    mapConstants q k k' (algebraMap k (CoordRing q k) c) = algebraMap k' (CoordRing q k') (algebraMap k k' c) := by
  rw [← (mk q k).commutes c, mapConstants_mk, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  exact (mk q k').commutes _

private def retract (r : k' →ₗ[k] k) (f : MvPolynomial (Fin 2) k') : MvPolynomial (Fin 2) k :=
  ∑ m ∈ f.support, monomial m (r (coeff m f))

private theorem coeff_retract (r : k' →ₗ[k] k) (f : MvPolynomial (Fin 2) k') (m : Fin 2 →₀ ℕ) :
    coeff m (retract k k' r f) = r (coeff m f) := by
  simp only [retract, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [mem_support_iff, not_not] at h
    rw [h, map_zero]

private theorem retract_mul_map (r : k' →ₗ[k] k) (f : MvPolynomial (Fin 2) k') (g : MvPolynomial (Fin 2) k) :
    retract k k' r (f * MvPolynomial.map (algebraMap k k') g) = retract k k' r f * g := by
  ext m
  simp only [coeff_retract, coeff_mul, coeff_map, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

private theorem retract_map (r : k' →ₗ[k] k) (hr : ∀ c : k, r (algebraMap k k' c) = c)
    (g : MvPolynomial (Fin 2) k) : retract k k' r (MvPolynomial.map (algebraMap k k') g) = g := by
  ext m
  rw [coeff_retract, coeff_map, hr]

theorem mapConstants_injective : Function.Injective (mapConstants q k k') := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap k k').exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
  have hr' : ∀ c : k, r (algebraMap k k' c) = c := fun c => by
    simpa using LinearMap.congr_fun hr c
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, rfl⟩ := mk_surjective q k z
  rw [mapConstants_mk] at hz
  have ha : MvPolynomial.map (algebraMap k k') a ∈ drinfeldIdeal q k' := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [drinfeldIdeal, Ideal.mem_span_singleton'] at ha
  obtain ⟨b, hb⟩ := ha
  have hrel : drinfeldPoly q k' - 1 = MvPolynomial.map (algebraMap k k') (drinfeldPoly q k - 1) := by
    rw [map_sub, map_one, map_drinfeldPoly]
  have ha' : a = retract k k' r b * (drinfeldPoly q k - 1) := by
    rw [← retract_mul_map, ← hrel, hb, retract_map k k' r hr']
  have hmem : a ∈ drinfeldIdeal q k := by
    rw [ha', drinfeldIdeal]
    exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

end CoordRing

def functionFieldMapConstants [IsDomain (CoordRing q k')] :
    drinfeldFunctionField q k →+* drinfeldFunctionField q k' :=
  IsFractionRing.map (CoordRing.mapConstants_injective q k k')

theorem functionFieldMapConstants_algebraMap [IsDomain (CoordRing q k')] (a : CoordRing q k) :
    functionFieldMapConstants q k k' (algebraMap (CoordRing q k) (drinfeldFunctionField q k) a) =
      algebraMap (CoordRing q k') (drinfeldFunctionField q k') (CoordRing.mapConstants q k k' a) := by
  unfold functionFieldMapConstants IsFractionRing.map
  exact IsLocalization.map_eq _ a

@[reducible] def constantsAlgebraCoordRing : Algebra k (CoordRing q k') :=
  ((algebraMap k' (CoordRing q k')).comp (algebraMap k k')).toAlgebra

@[reducible] def constantsAlgebraFunctionField : Algebra k (drinfeldFunctionField q k') :=
  letI := constantsAlgebraCoordRing q k k'
  inferInstanceAs (Algebra k (FractionRing (CoordRing q k')))

@[reducible] def functionFieldConstantsAlgebra [IsDomain (CoordRing q k')] :
    Algebra (drinfeldFunctionField q k) (drinfeldFunctionField q k') :=
  (functionFieldMapConstants q k k').toAlgebra

attribute [local instance 10] constantsAlgebraCoordRing functionFieldConstantsAlgebra

theorem algebraMap_drinfeldFunctionField_eq [IsDomain (CoordRing q k')] :
    algebraMap (drinfeldFunctionField q k) (drinfeldFunctionField q k') = functionFieldMapConstants q k k' :=
  rfl

scoped instance instTowerConstantsFunctionField :
    @IsScalarTower k k' (drinfeldFunctionField q k')
      (Algebra.toSMul (R := k) (A := k'))
      (Algebra.toSMul (R := k') (A := drinfeldFunctionField q k'))
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k')) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance instTowerFunctionFieldConstants [IsDomain (CoordRing q k')] :
    @IsScalarTower k (drinfeldFunctionField q k) (drinfeldFunctionField q k')
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k))
      (Algebra.toSMul (R := drinfeldFunctionField q k) (A := drinfeldFunctionField q k'))
      (Algebra.toSMul (R := k) (A := drinfeldFunctionField q k')) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_drinfeldFunctionField_eq,
      IsScalarTower.algebraMap_apply k (CoordRing q k) (drinfeldFunctionField q k) c,
      functionFieldMapConstants_algebraMap, CoordRing.mapConstants_algebraMap]
    rfl

theorem finiteType_coordRing : Algebra.FiniteType k (CoordRing q k) :=
  Algebra.FiniteType.of_surjective (mk q k) (mk_surjective q k)

theorem essFiniteType_drinfeldFunctionField : Algebra.EssFiniteType k (drinfeldFunctionField q k) :=
  haveI := finiteType_coordRing q k
  inferInstance

private theorem algebraMap_coordRing_mem_adjoin [IsDomain (CoordRing q k')] (a : CoordRing q k') :
    algebraMap (CoordRing q k') (drinfeldFunctionField q k') a ∈
      Algebra.adjoin (drinfeldFunctionField q k) (Set.range (algebraMap k' (drinfeldFunctionField q k'))) := by
  obtain ⟨f, rfl⟩ := mk_surjective q k' a
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, (mk q k').commutes,
      ← IsScalarTower.algebraMap_apply k' (CoordRing q k') (drinfeldFunctionField q k')]
    exact Algebra.subset_adjoin ⟨c, rfl⟩
  | add f g hf hg =>
    rw [map_add, map_add]
    exact Subalgebra.add_mem _ hf hg
  | mul_X f i hf =>
    rw [map_mul, map_mul]
    refine Subalgebra.mul_mem _ hf ?_
    have hX : mk q k' (X i) = CoordRing.mapConstants q k k' (mk q k (X i)) := by
      rw [CoordRing.mapConstants_mk, MvPolynomial.map_X]
    rw [hX, ← functionFieldMapConstants_algebraMap, ← algebraMap_drinfeldFunctionField_eq]
    exact Subalgebra.algebraMap_mem _ _

private theorem adjoin_range_algebraMap_le_integralClosure [IsDomain (CoordRing q k')]
    [Algebra.IsAlgebraic k k'] :
    Algebra.adjoin (drinfeldFunctionField q k) (Set.range (algebraMap k' (drinfeldFunctionField q k'))) ≤
      integralClosure (drinfeldFunctionField q k) (drinfeldFunctionField q k') := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c, rfl⟩
  have hc : IsIntegral k (algebraMap k' (drinfeldFunctionField q k') c) :=
    (Algebra.IsIntegral.isIntegral (R := k) c).map (IsScalarTower.toAlgHom k k' (drinfeldFunctionField q k'))
  exact (mem_integralClosure_iff _ _).mpr hc.tower_top

theorem adjoin_range_algebraMap_eq_top [IsDomain (CoordRing q k)] [IsDomain (CoordRing q k')]
    [Algebra.IsAlgebraic k k'] :
    Algebra.adjoin (drinfeldFunctionField q k) (Set.range (algebraMap k' (drinfeldFunctionField q k'))) = ⊤ := by
  refine top_unique fun z _ => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := CoordRing q k') z
  rw [div_eq_mul_inv]
  refine Subalgebra.mul_mem _ (algebraMap_coordRing_mem_adjoin q k k' a) ?_
  have hb := algebraMap_coordRing_mem_adjoin q k k' b
  have hint : IsIntegral (drinfeldFunctionField q k)
      (algebraMap (CoordRing q k') (drinfeldFunctionField q k') b) :=
    (mem_integralClosure_iff _ _).mp (adjoin_range_algebraMap_le_integralClosure q k k' hb)
  exact Subalgebra.inv_mem_of_algebraic _ (x := ⟨_, hb⟩) hint.isAlgebraic

theorem isIntegral_functionFieldMapConstants [IsDomain (CoordRing q k)] [IsDomain (CoordRing q k')]
    [Algebra.IsAlgebraic k k'] :
    Algebra.IsIntegral (drinfeldFunctionField q k) (drinfeldFunctionField q k') := by
  refine ⟨fun z => (mem_integralClosure_iff _ _).mp (adjoin_range_algebraMap_le_integralClosure q k k' ?_)⟩
  rw [adjoin_range_algebraMap_eq_top q k k']
  exact Algebra.mem_top

section Equivariance

variable [Fact q.Prime] [Algebra (GaloisField q 2) k] [Algebra (GaloisField q 2) k']
  [IsScalarTower (GaloisField q 2) k k']

theorem algebraMap_ofZMod (a : ZMod q) : algebraMap k k' (ofZMod q k a) = ofZMod q k' a := by
  simp only [ofZMod, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply (GaloisField q 2) k k']

theorem algebraMap_scalarOf (ζ : (GaloisField q 2)ˣ) : algebraMap k k' (scalarOf q k ζ) = scalarOf q k' ζ := by
  simp only [scalarOf]
  rw [← IsScalarTower.algebraMap_apply (GaloisField q 2) k k']

theorem map_substPoly (g : Matrix (Fin 2) (Fin 2) (ZMod q)) (f : MvPolynomial (Fin 2) k) :
    MvPolynomial.map (algebraMap k k') (substPoly q k g f) =
      substPoly q k' g (MvPolynomial.map (algebraMap k k') f) := by
  have hcomp : (MvPolynomial.map (algebraMap k k')).comp
        (substPoly q k g : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) =
      (substPoly q k' g : MvPolynomial (Fin 2) k' →+* MvPolynomial (Fin 2) k').comp
        (MvPolynomial.map (algebraMap k k')) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.algHom_C]
    · intro j
      simp [substPoly_X, algebraMap_ofZMod]
  exact RingHom.congr_fun hcomp f

theorem map_scalePoly (c : k) (f : MvPolynomial (Fin 2) k) :
    MvPolynomial.map (algebraMap k k') (scalePoly k c f) =
      scalePoly k' (algebraMap k k' c) (MvPolynomial.map (algebraMap k k') f) := by
  have hcomp : (MvPolynomial.map (algebraMap k k')).comp
        (scalePoly k c : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 2) k) =
      (scalePoly k' (algebraMap k k' c) : MvPolynomial (Fin 2) k' →+* MvPolynomial (Fin 2) k').comp
        (MvPolynomial.map (algebraMap k k')) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.algHom_C]
    · intro j
      simp [scalePoly_X]
  exact RingHom.congr_fun hcomp f

theorem CoordRing.mapConstants_hAction (p : hSubgroup q) (z : CoordRing q k) :
    CoordRing.mapConstants q k k' (hAction q k p z) = hAction q k' p (CoordRing.mapConstants q k k' z) := by
  obtain ⟨f, rfl⟩ := mk_surjective q k z
  rw [hAction_mk, CoordRing.mapConstants_mk, CoordRing.mapConstants_mk, hAction_mk, map_scalePoly, map_substPoly,
    algebraMap_scalarOf]

theorem functionFieldMapConstants_hAction [IsDomain (CoordRing q k')] (p : hSubgroup q)
    (f : drinfeldFunctionField q k) :
    functionFieldMapConstants q k k' (hFunctionFieldAction q k p f) =
      hFunctionFieldAction q k' p (functionFieldMapConstants q k k' f) := by
  have hcomp : (functionFieldMapConstants q k k').comp
        ((hFunctionFieldAction q k p : drinfeldFunctionField q k ≃ₐ[k] drinfeldFunctionField q k) :
          drinfeldFunctionField q k →+* drinfeldFunctionField q k) =
      ((hFunctionFieldAction q k' p : drinfeldFunctionField q k' ≃ₐ[k'] drinfeldFunctionField q k') :
          drinfeldFunctionField q k' →+* drinfeldFunctionField q k').comp (functionFieldMapConstants q k k') := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (CoordRing q k))
    ext a
    simp [hFunctionFieldAction_algebraMap, functionFieldMapConstants_algebraMap, CoordRing.mapConstants_hAction]
  exact RingHom.congr_fun hcomp f

theorem intertwinesAlong_functionFieldMapConstants [IsDomain (CoordRing q k)] [IsDomain (CoordRing q k')]
    (p : hSubgroup q) :
    AlgebraicCurve.SemilinearAut.IntertwinesAlong (functionFieldMapConstants q k k')
      (AlgebraicCurve.SemilinearAut.ofAlgAut (hFunctionFieldAction q k p))
      (AlgebraicCurve.SemilinearAut.ofAlgAut ((hFunctionFieldAction q k' p).restrictScalars k)) :=
  fun f => (functionFieldMapConstants_hAction q k k' p f).symm

end Equivariance

end Square

end DrinfeldCurve

end

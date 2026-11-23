module

public import Mathlib
public import Theorem.Submodule.ContinuousUnramifiedLevel
public import Instance.GroupCohomology_LevelSubgroup
public import Theorem.Rep.ContinuousH2Inflation

public noncomputable section

set_option autoImplicit false

open CategoryTheory

noncomputable section
namespace groupCohomology

section A0
variable {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (M : Rep.{0} k G) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

omit [Normal ℚ F] in
public theorem coe_mul_eq_of_mem' {g s : G} (hs : r s ∈ F.fixingSubgroup) :
    ((g * s : G) : G ⧸ F.fixingSubgroup.comap r) = (g : G ⧸ F.fixingSubgroup.comap r) := by
  rw [QuotientGroup.eq]; simpa using (F.fixingSubgroup.comap r).inv_mem hs


public theorem levelInflate₁_mem_levelCochainsSr₁ (hF : F.IsUnramifiedOutside S) (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₁ r M F y ∈ levelCochainsSr₁ r S M :=
  ⟨F, hF, fun g s hs => by simp only [levelInflate₁_apply, coe_mul_eq_of_mem' r F hs]⟩


public theorem levelInflate₂_mem_levelCocyclesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCocyclesSr₂ r S M :=
  ⟨levelInflate₂_mem_cocycles₂ hx, ⟨F, hF, fun g g' s s' hs hs' => by
    simp only [levelInflate₂_apply, coe_mul_eq_of_mem' r F hs, coe_mul_eq_of_mem' r F hs']⟩⟩


public theorem levelInflate₂_mem_levelCoboundariesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCoboundariesSr₂ r S M := by
  obtain ⟨y, rfl⟩ := hx
  exact (mem_levelCoboundariesSr₂_iff r S M _).2 ⟨levelInflate₁ r M F y, levelInflate₁_mem_levelCochainsSr₁ r S M F hF y, (levelInflate₂_d₁₂ y).symm⟩


public theorem coe_levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    (levelInflateCocyclesSr₂ r S M F hF x : G × G → M) = levelInflate₂ r M F x := rfl


public theorem continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero (hF : F.IsUnramifiedOutside S)
    {x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))}
    (hx : (x : _ → _) ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) = 0 :=
  (continuousH2Srπ_eq_zero_iff r S M _).2 (levelInflate₂_mem_levelCoboundariesSr₂ r S M F hF hx)


public theorem continuousH2SrInflation_H2π (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ x) = continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) := by
  simp [continuousH2SrInflation, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end A0

end groupCohomology
end

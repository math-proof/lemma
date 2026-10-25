/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/Ado.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Def.Algebra.Lie.LeviDecomposition.Part15
import Lemma.Fin.EqSum_SMul.of.Basis
import Def.Algebra.Lie.Ado.Part7
attribute [local instance 100] LieRing.ofAssociativeRing

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/


namespace MathlibExt.Algebra.Lie.LandmarkWanted

theorem adoSemidirectQuotient_right_isNilpotent
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
    (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
    (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
    [Module.Finite K (adoUEA K I ⧸
      (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)]
    (h : H) (hD : IsNilpotent (ψ h).toLinearMap) :
    IsNilpotent
      (adoQuotientRepresentation (adoSemidirectRepresentation ψ)
        ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
        (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨0, h⟩) := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  let d : Module.End K (adoUEA K I) := adoExtendDerivation (ψ h)
  have hdQ : qK ≤ qK.comap d := hQ h
  have hlocal : ∀ u, ∃ n, (d ^ n) u = 0 := by
    exact adoUEA_derivation_locallyNilpotent (ψ h).toLinearMap d
      (adoExtendDerivation_mul (ψ h)) (adoExtendDerivation_ι (ψ h)) hD
  have hnil := adoQuotient_end_isNilpotent d qK hdQ hlocal
  have hrep : adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H) = d := by
    ext u
    change UniversalEnvelopingAlgebra.ι K 0 * u +
      adoExtendDerivation (ψ h) u = adoExtendDerivation (ψ h) u
    simp
  have hmap : qK.mapQ qK
      (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H))
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨0, h⟩) =
      qK.mapQ qK d hdQ := by
    ext u
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H) u) :
        adoUEA K I ⧸ qK) = Submodule.Quotient.mk (d u)
    rw [hrep]
  change IsNilpotent (qK.mapQ qK
    (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H))
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨0, h⟩))
  rw [hmap]
  exact hnil

theorem adoNilpotent_representation
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieRing.IsNilpotent L] :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ ∧ ∀ x, IsNilpotent (ρ x) := by
  classical
  by_cases hab : IsLieAbelian L
  · let _ : IsLieAbelian L := hab
    apply ado_transport_fin_nilpotent (adoAbelianShear (K := K) (L := L))
      adoAbelianShear_injective
    intro x
    refine ⟨2, ?_⟩
    rw [pow_two, adoAbelianShear_mul_eq_zero]
  · obtain ⟨A, hA, hder, h, hh⟩ :=
      adoNilpotent_exists_coatom (K := K) (L := L) hab
    let _ : Nontrivial A := adoCoatom_nontrivial (K := K) A hder hab
    have hfin : Module.finrank K A < Module.finrank K L := by
      rw [← finrank_top K L]
      exact Submodule.finrank_lt_finrank_of_lt hA.lt_top
    have hAincl : Function.Injective A.incl := fun x y hxy => Subtype.ext hxy
    let _ : LieRing.IsNilpotent A := hAincl.lieAlgebra_isNilpotent
    obtain ⟨n, ρ₀, hρ₀, hnil₀⟩ :=
      adoNilpotent_representation (K := K) (L := A)
    let V := Fin n → K
    let _ : LieRingModule A V := LieRingModule.compLieHom V ρ₀
    let _ : LieModule K A V := LieModule.compLieHom V ρ₀
    have hVnil : LieModule.IsNilpotent A V := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro a
      change IsNilpotent (ρ₀ a)
      exact hnil₀ a
    obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K A V).mp hVnil
    let S : Set (adoUEA K A) := Set.range (UniversalEnvelopingAlgebra.ι K)
    let T : Ideal (adoUEA K A) := (TwoSidedIdeal.span S).asIdeal
    let Q : Ideal (adoUEA K A) := T ^ k
    have hgen (a : A) : UniversalEnvelopingAlgebra.ι K a ∈ T := by
      exact TwoSidedIdeal.mem_asIdeal.mpr
        (TwoSidedIdeal.subset_span ⟨a, rfl⟩)
    have hS : ∀ s ∈ S, ∀ j v, v ∈ (⊤ : LieIdeal K A).lcs V j →
        UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K A V) s v ∈
          (⊤ : LieIdeal K A).lcs V (j + 1) := by
      rintro _ ⟨a, rfl⟩ j v hv
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      change ⁅a, v⁆ ∈ (⊤ : LieIdeal K A).lcs V (j + 1)
      rw [LieIdeal.lcs_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) hv
    have hk' : (⊤ : LieIdeal K A).lcs V k = ⊥ := by
      rw [LieIdeal.lcs_top]
      exact hk
    have hQker :
        (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K ≤
          LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
      have htoEnd : LieModule.toEnd K A V = ρ₀ := by rfl
      simpa only [Q, T, S, htoEnd] using
        (adoIdealPower_le_ker_lift (I := (⊤ : LieIdeal K A)) S hS k hk')
    let H : LieSubalgebra K L := adoLineSubalgebra (K := K) h
    have hc : IsCompl A.toSubmodule H.toSubmodule := by
      change IsCompl A.toSubmodule (K ∙ h)
      exact Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
    let ψ : H →ₗ⁅K⁆ LieDerivation K A A := (adoIdealAd A).comp H.incl
    have hT (z : H) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
      apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
        (adoExtendDerivation_mul (ψ z)) T
      intro a
      rw [adoExtendDerivation_ι]
      exact hgen ((ψ z) a)
    have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
      intro z u hu
      change adoExtendDerivation (ψ z) u ∈ T ^ k
      exact adoUEA_derivation_preserves_idealPower
        (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
        T (hT z) k hu
    let b := Module.finBasis K A
    let _ : NeZero (Module.finrank K A) := NeZero.of_pos Module.finrank_pos
    have hpow (i : Fin (Module.finrank K A)) :
        (UniversalEnvelopingAlgebra.ι K (b i)) ^ k ∈ adoModWords Q b k := by
      apply Submodule.mem_sup_left
      change (UniversalEnvelopingAlgebra.ι K (b i)) ^ k ∈ T ^ k
      exact Ideal.pow_mem_pow (hgen (b i)) k
    let qK := (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K
    let _ : Module.Finite K (adoUEA K A ⧸ qK) :=
      adoQuotient_finite_of_power_relations Q b hpow
    let ρQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) :=
      adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
        (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
    let e : (A ⋊⁅ψ⁆ H) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl A H hc
    let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) := ρQ.comp e.symm
    let hH : H := ⟨h, Submodule.mem_span_singleton_self h⟩
    have heA (a : A) : e.symm a.1 = (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv a.1) = a.1 :=
          e.apply_symm_apply a.1
        _ = e.toLinearEquiv (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
          change a.1 = a.1 + 0
          simp
    have heh : e.symm h = (⟨0, hH⟩ : A ⋊⁅ψ⁆ H) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv h) = h :=
          e.apply_symm_apply h
        _ = e.toLinearEquiv (⟨0, hH⟩ : A ⋊⁅ψ⁆ H) := by
          change h = 0 + h
          simp
    let _ : LieRingModule L (adoUEA K A ⧸ qK) :=
      LieRingModule.compLieHom (adoUEA K A ⧸ qK) ρL
    let _ : LieModule K L (adoUEA K A ⧸ qK) :=
      LieModule.compLieHom (adoUEA K A ⧸ qK) ρL
    have hAnil : LieModule.IsNilpotent A (adoUEA K A ⧸ qK) := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro a
      change IsNilpotent (ρL a.1)
      have haQ := adoSemidirectQuotient_left_isNilpotent ψ Q hQ a k
        (show (UniversalEnvelopingAlgebra.ι K a) ^ k ∈ Q from
          Ideal.pow_mem_pow (hgen a) k)
      change IsNilpotent (ρQ (e.symm a.1))
      rw [heA]
      exact haQ
    have had : IsNilpotent (LieModule.toEnd K L L h) :=
      (LieModule.isNilpotent_iff_forall' (R := K)).mp
        (inferInstanceAs (LieRing.IsNilpotent L)) h
    have hD : IsNilpotent (ψ hH).toLinearMap := by
      change IsNilpotent (LieModule.toEnd K L A h)
      exact Module.End.isNilpotent.restrict (fun _ ha => A.lie_mem ha) had
    have hhnil : IsNilpotent (LieModule.toEnd K L (adoUEA K A ⧸ qK) h) := by
      change IsNilpotent (ρL h)
      have hhQ := adoSemidirectQuotient_right_isNilpotent ψ Q hQ hH hD
      change IsNilpotent (ρQ (e.symm h))
      rw [heh]
      exact hhQ
    have hLnil : LieModule.IsNilpotent L (adoUEA K A ⧸ qK) :=
      adoNilpotent_of_codim_one_extension A h
        (adoCoatom_decomp A hA h hh) hAnil hhnil
    let _ : IsLieAbelian H := adoLine_isLieAbelian h
    let σQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (H × K) :=
      (adoAbelianShear (K := K) (L := H)).comp
        (LieAlgebra.SemiDirectSum.projr ψ)
    let σL : L →ₗ⁅K⁆ Module.End K (H × K) := σQ.comp e.symm
    let ρ := adoDirectSum ρL σL
    have hρ : Function.Injective ρ := by
      intro x y hxy
      have hzero : ρ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨hleft, hright⟩ :=
        (adoDirectSum_eq_zero_iff ρL σL (x - y)).mp hzero
      let z := e.symm (x - y)
      have hzright : z.right = 0 := by
        apply adoAbelianShear_injective (K := K) (L := H)
        simpa [σL, σQ, z] using hright
      have hzleft : z.left = 0 := by
        apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
        change ρQ ⟨z.left, 0⟩ = 0
        have hz : z = (⟨z.left, 0⟩ : A ⋊⁅ψ⁆ H) := by
          ext <;> simp [hzright]
        change ρQ (e.symm (x - y)) = 0 at hleft
        change ρQ z = 0 at hleft
        rw [hz] at hleft
        exact hleft
      have hz : z = 0 := by ext <;> simp [hzleft, hzright]
      apply sub_eq_zero.mp
      have hez : e z = x - y := by
        dsimp [z]
        exact e.apply_symm_apply (x - y)
      calc
        x - y = e z := hez.symm
        _ = 0 := by rw [hz, map_zero]
    have hρnil : ∀ x, IsNilpotent (ρ x) := by
      intro x
      apply adoDirectSum_isNilpotent ρL σL
      · change IsNilpotent (LieModule.toEnd K L (adoUEA K A ⧸ qK) x)
        exact (LieModule.isNilpotent_iff_forall' (R := K)).mp hLnil x
      · refine ⟨2, ?_⟩
        rw [pow_two]
        change adoAbelianShear (K := K) (e.symm x).right *
          adoAbelianShear (K := K) (e.symm x).right = 0
        exact adoAbelianShear_mul_eq_zero _ _
    exact ado_transport_fin_nilpotent ρ hρ hρnil
termination_by Module.finrank K L
decreasing_by exact hfin

theorem adoSolvable_representation
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSolvable L]
    (N : LieIdeal K L) [LieRing.IsNilpotent N]
    (hderived : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ N.toSubmodule) :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ ∧ ∀ x : N, IsNilpotent (ρ x.1) := by
  classical
  by_cases hab : IsLieAbelian L
  · let _ : IsLieAbelian L := hab
    obtain ⟨n, ρ, hρ, hnil⟩ :=
      ado_transport_fin_nilpotent (adoAbelianShear (K := K) (L := L))
        adoAbelianShear_injective (fun x => ⟨2, by
          rw [pow_two, adoAbelianShear_mul_eq_zero]⟩)
    exact ⟨n, ρ, hρ, fun x => hnil x.1⟩
  · by_cases hN : N = ⊤
    · have hsurj : Function.Surjective N.incl := by
        intro x
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [hN]
        exact LieSubmodule.mem_top x
      let _ : LieRing.IsNilpotent L := hsurj.lieAlgebra_isNilpotent
      obtain ⟨n, ρ, hρ, hnil⟩ := adoNilpotent_representation (K := K) (L := L)
      exact ⟨n, ρ, hρ, fun x => hnil x.1⟩
    · obtain ⟨A, hA, hNA, h, hh⟩ :=
        adoIdeal_exists_coatom N hderived hN
      let _ : Nontrivial A := adoCoatom_nontrivial A
        (fun _ hx => hNA (hderived hx)) hab
      have hfin : Module.finrank K A < Module.finrank K L := by
        rw [← finrank_top K L]
        exact Submodule.finrank_lt_finrank_of_lt hA.lt_top
      let NA : LieIdeal K A := N.comap A.incl
      let fNA : NA →ₗ⁅K⁆ N :=
        { toLinearMap :=
            { toFun := fun x => ⟨x.1.1, x.2⟩
              map_add' := by intros; rfl
              map_smul' := by intros; rfl }
          map_lie' := by intros; rfl }
      have hfNA : Function.Injective fNA := by
        intro x y hxy
        exact Subtype.ext (Subtype.ext
          (congrArg (fun z : N => (z.1 : L)) hxy))
      let _ : LieRing.IsNilpotent NA := hfNA.lieAlgebra_isNilpotent
      have hderivedA :
          (LieAlgebra.derivedSeries K A 1 : Submodule K A) ≤ NA.toSubmodule := by
        intro x hx
        change x.1 ∈ N
        apply hderived
        apply LieIdeal.derivedSeries_map_le (f := A.incl) 1
        exact LieIdeal.mem_map hx
      obtain ⟨n, ρ₀, hρ₀, hnil₀⟩ :=
        adoSolvable_representation NA hderivedA
      let V := Fin n → K
      let _ : LieRingModule A V := LieRingModule.compLieHom V ρ₀
      let _ : LieModule K A V := LieModule.compLieHom V ρ₀
      have hVnil : LieModule.IsNilpotent NA V := by
        rw [LieModule.isNilpotent_iff_forall' (R := K)]
        intro x
        change IsNilpotent (ρ₀ x.1)
        exact hnil₀ x
      obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K NA V).mp hVnil
      let b := Module.finBasis K A
      let p (i : Fin (Module.finrank K A)) : Polynomial K :=
        Polynomial.X * (ρ₀ (b i)).charpoly
      let rel (i : Fin (Module.finrank K A)) : adoUEA K A :=
        Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) (p i)
      let S : Set (adoUEA K A) :=
        Set.range (fun x : NA => UniversalEnvelopingAlgebra.ι K x.1) ∪
          Set.range rel
      let T : Ideal (adoUEA K A) := (TwoSidedIdeal.span S).asIdeal
      let Q : Ideal (adoUEA K A) := T ^ k
      have hgenN (x : NA) : UniversalEnvelopingAlgebra.ι K x.1 ∈ T := by
        exact TwoSidedIdeal.mem_asIdeal.mpr
          (TwoSidedIdeal.subset_span (Set.mem_union_left _ ⟨x, rfl⟩))
      have hgenRel (i : Fin (Module.finrank K A)) : rel i ∈ T := by
        exact TwoSidedIdeal.mem_asIdeal.mpr
          (TwoSidedIdeal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
      have hS : ∀ s ∈ S, ∀ j v, v ∈ NA.lcs V j →
          UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K A V) s v ∈
            NA.lcs V (j + 1) := by
        intro s hs
        rcases hs with hs | hs
        · obtain ⟨x, rfl⟩ := hs
          intro j v hv
          rw [UniversalEnvelopingAlgebra.lift_ι_apply]
          change ⁅x.1, v⁆ ∈ NA.lcs V (j + 1)
          rw [LieIdeal.lcs_succ]
          exact LieSubmodule.lie_mem_lie x.2 hv
        · obtain ⟨i, rfl⟩ := hs
          intro j v hv
          have hzero : UniversalEnvelopingAlgebra.lift K
              (LieModule.toEnd K A V) (rel i) = 0 := by
            dsimp [rel]
            rw [← Polynomial.aeval_algHom_apply,
              UniversalEnvelopingAlgebra.lift_ι_apply]
            change Polynomial.aeval (ρ₀ (b i)) (p i) = 0
            simp [p, LinearMap.aeval_self_charpoly]
          rw [hzero, LinearMap.zero_apply]
          exact (NA.lcs V (j + 1)).zero_mem
      have hk' : NA.lcs V k = ⊥ := by
        rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq]
        exact congrArg LieSubmodule.toSubmodule hk
      have hQker :
          (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K ≤
            LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
        have htoEnd : LieModule.toEnd K A V = ρ₀ := by rfl
        simpa only [Q, T, htoEnd] using
          (adoIdealPower_le_ker_lift NA S hS k hk')
      let H : LieSubalgebra K L := adoLineSubalgebra (K := K) h
      have hc : IsCompl A.toSubmodule H.toSubmodule := by
        change IsCompl A.toSubmodule (K ∙ h)
        exact Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
      let ψ : H →ₗ⁅K⁆ LieDerivation K A A := (adoIdealAd A).comp H.incl
      have hT (z : H) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
        apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
          (adoExtendDerivation_mul (ψ z)) T
        intro a
        rw [adoExtendDerivation_ι]
        have hza : (ψ z a).1 ∈ N := by
          apply hderived
          exact LieSubmodule.lie_mem_lie
            (LieSubmodule.mem_top z.1) (LieSubmodule.mem_top a.1)
        exact hgenN ⟨ψ z a, hza⟩
      have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
        intro z u hu
        change adoExtendDerivation (ψ z) u ∈ T ^ k
        exact adoUEA_derivation_preserves_idealPower
          (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
          T (hT z) k hu
      let B := k * (Module.finrank K V + 1)
      let _ : NeZero (Module.finrank K A) := NeZero.of_pos Module.finrank_pos
      have hp (i : Fin (Module.finrank K A)) : (p i).Monic := by
        exact Polynomial.monic_X.mul (LinearMap.charpoly_monic (ρ₀ (b i)))
      have hdegree (i : Fin (Module.finrank K A)) : (p i ^ k).natDegree = B := by
        rw [(hp i).natDegree_pow]
        simp [p, B, V, LinearMap.charpoly_natDegree,
          (LinearMap.charpoly_monic (ρ₀ (b i))).ne_zero]
      have hpow (i : Fin (Module.finrank K A)) :
          (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B := by
        have hrelpow : Polynomial.aeval
            (UniversalEnvelopingAlgebra.ι K (b i)) (p i ^ k) ∈ Q := by
          rw [map_pow]
          exact Ideal.pow_mem_pow (hgenRel i) k
        have hm := adoAeval_monic_mem_modWords Q b i (p i ^ k)
          ((hp i).pow k) hrelpow
        rwa [hdegree i] at hm
      let qK := (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K
      let _ : Module.Finite K (adoUEA K A ⧸ qK) :=
        adoQuotient_finite_of_power_relations Q b hpow
      let ρQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) :=
        adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
          (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
      let e : (A ⋊⁅ψ⁆ H) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl A H hc
      let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) := ρQ.comp e.symm
      let _ : IsLieAbelian H := adoLine_isLieAbelian h
      let σQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (H × K) :=
        (adoAbelianShear (K := K) (L := H)).comp
          (LieAlgebra.SemiDirectSum.projr ψ)
      let σL : L →ₗ⁅K⁆ Module.End K (H × K) := σQ.comp e.symm
      let ρ := adoDirectSum ρL σL
      have hρ : Function.Injective ρ := by
        intro x y hxy
        have hzero : ρ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨hleft, hright⟩ :=
          (adoDirectSum_eq_zero_iff ρL σL (x - y)).mp hzero
        let z := e.symm (x - y)
        have hzright : z.right = 0 := by
          apply adoAbelianShear_injective (K := K) (L := H)
          simpa [σL, σQ, z] using hright
        have hzleft : z.left = 0 := by
          apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
          change ρQ ⟨z.left, 0⟩ = 0
          have hz : z = (⟨z.left, 0⟩ : A ⋊⁅ψ⁆ H) := by
            ext <;> simp [hzright]
          change ρQ (e.symm (x - y)) = 0 at hleft
          change ρQ z = 0 at hleft
          rw [hz] at hleft
          exact hleft
        have hz : z = 0 := by ext <;> simp [hzleft, hzright]
        apply sub_eq_zero.mp
        have hez : e z = x - y := by
          dsimp [z]
          exact e.apply_symm_apply (x - y)
        calc
          x - y = e z := hez.symm
          _ = 0 := by rw [hz, map_zero]
      have hρnil : ∀ x : N, IsNilpotent (ρ x.1) := by
        intro x
        let a : A := ⟨x.1, hNA x.2⟩
        let xA : NA := ⟨a, x.2⟩
        have hea : e.symm x.1 = (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
          apply e.toLinearEquiv.injective
          calc
            e.toLinearEquiv (e.symm.toLinearEquiv x.1) = x.1 :=
              e.apply_symm_apply x.1
            _ = e.toLinearEquiv (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
              change x.1 = a.1 + 0
              simp [a]
        apply adoDirectSum_isNilpotent ρL σL
        · change IsNilpotent (ρQ (e.symm x.1))
          rw [hea]
          apply adoSemidirectQuotient_left_isNilpotent ψ Q hQ a k
          exact Ideal.pow_mem_pow (hgenN xA) k
        · refine ⟨2, ?_⟩
          rw [pow_two]
          change adoAbelianShear (K := K) (e.symm x.1).right *
            adoAbelianShear (K := K) (e.symm x.1).right = 0
          exact adoAbelianShear_mul_eq_zero _ _
      exact ado_transport_fin_nilpotent_on N ρ hρ hρnil
termination_by Module.finrank K L
decreasing_by exact hfin

/--
Every finite-dimensional Lie algebra `L` over a field `K` of characteristic zero admits a faithful
finite-dimensional representation `ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)` that is injective.
Source: I. D. Ado, Bull. Soc. Phys.-Math. Kazan 7 (1935) and 1947 char-zero theorem; Bourbaki, Lie
Groups and Lie Algebras; Lean states char-zero finite-dimensional version while modern theorem
extends to arbitrary fields.

Proves `Wanted` entry `ado`.

Proof: Following Tao's 2011 route, the nilpotent and solvable cases are proved by induction using
finite-dimensional quotients of universal enveloping algebras. The general case uses the Levi
decomposition and combines the resulting radical representation with the adjoint representation.
-/
theorem ado
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ := by
  classical
  let R : LieIdeal K L := LieAlgebra.radical K L
  let J : LieIdeal K L := adoCommutatorIdeal R
  let _ : LieRing.IsNilpotent J := adoCommutator_isNilpotent R
  let N : LieIdeal K L := J + LieAlgebra.center K L
  let _ : LieRing.IsNilpotent N := adoAdd_center_isNilpotent J
  let NR : LieIdeal K R := N.comap R.incl
  let fNR : NR →ₗ⁅K⁆ N :=
    { toLinearMap :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      map_lie' := by intros; rfl }
  have hfNR : Function.Injective fNR := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : N => (z.1 : L)) hxy))
  let _ : LieRing.IsNilpotent NR := hfNR.lieAlgebra_isNilpotent
  have hderivedR :
      (LieAlgebra.derivedSeries K R 1 : Submodule K R) ≤ NR.toSubmodule := by
    intro x hx
    change x.1 ∈ N
    have hxmap : R.incl x ∈ (LieAlgebra.derivedSeries K R 1).map R.incl :=
      LieIdeal.mem_map hx
    rw [R.derivedSeries_eq_derivedSeriesOfIdeal_map,
      LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero] at hxmap
    exact Submodule.mem_sup_left (LieSubmodule.mono_lie le_top le_rfl hxmap)
  obtain ⟨m, ρ₀, hρ₀, hnil₀⟩ :=
    adoSolvable_representation NR hderivedR
  let V := Fin m → K
  let _ : LieRingModule R V := LieRingModule.compLieHom V ρ₀
  let _ : LieModule K R V := LieModule.compLieHom V ρ₀
  have hVnil : LieModule.IsNilpotent NR V := by
    rw [LieModule.isNilpotent_iff_forall' (R := K)]
    intro x
    change IsNilpotent (ρ₀ x.1)
    exact hnil₀ x
  obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K NR V).mp hVnil
  let b := Module.finBasis K R
  let p (i : Fin (Module.finrank K R)) : Polynomial K :=
    Polynomial.X * (ρ₀ (b i)).charpoly
  let rel (i : Fin (Module.finrank K R)) : adoUEA K R :=
    Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) (p i)
  let G : Set (adoUEA K R) :=
    Set.range (fun x : NR => UniversalEnvelopingAlgebra.ι K x.1) ∪
      Set.range rel
  let T : Ideal (adoUEA K R) := (TwoSidedIdeal.span G).asIdeal
  let Q : Ideal (adoUEA K R) := T ^ k
  have hgenN (x : NR) : UniversalEnvelopingAlgebra.ι K x.1 ∈ T := by
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (Set.mem_union_left _ ⟨x, rfl⟩))
  have hgenRel (i : Fin (Module.finrank K R)) : rel i ∈ T := by
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
  have hG : ∀ s ∈ G, ∀ j v, v ∈ NR.lcs V j →
      UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K R V) s v ∈
        NR.lcs V (j + 1) := by
    intro s hs
    rcases hs with hs | hs
    · obtain ⟨x, rfl⟩ := hs
      intro j v hv
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      change ⁅x.1, v⁆ ∈ NR.lcs V (j + 1)
      rw [LieIdeal.lcs_succ]
      exact LieSubmodule.lie_mem_lie x.2 hv
    · obtain ⟨i, rfl⟩ := hs
      intro j v hv
      have hzero : UniversalEnvelopingAlgebra.lift K
          (LieModule.toEnd K R V) (rel i) = 0 := by
        dsimp [rel]
        rw [← Polynomial.aeval_algHom_apply,
          UniversalEnvelopingAlgebra.lift_ι_apply]
        change Polynomial.aeval (ρ₀ (b i)) (p i) = 0
        simp [p, LinearMap.aeval_self_charpoly]
      rw [hzero, LinearMap.zero_apply]
      exact (NR.lcs V (j + 1)).zero_mem
  have hk' : NR.lcs V k = ⊥ := by
    rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq]
    exact congrArg LieSubmodule.toSubmodule hk
  have hQker :
      (Q : Submodule (adoUEA K R) (adoUEA K R)).restrictScalars K ≤
        LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
    have htoEnd : LieModule.toEnd K R V = ρ₀ := by rfl
    simpa only [Q, T, htoEnd] using
      (adoIdealPower_le_ker_lift NR G hG k hk')
  obtain ⟨C, -, hsum, hinter⟩ :=
    MathlibExt.Algebra.Lie.LandmarkWanted.levi_decomposition (K := K) (L := L)
  have hc : IsCompl R.toSubmodule C.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact hinter
    · rw [codisjoint_iff]
      change (LieAlgebra.radical K L).toSubmodule ⊔ C.toSubmodule = ⊤
      simpa only [Submodule.add_eq_sup,
        LieIdeal.toLieSubalgebra_toSubmodule] using hsum
  let ψ : C →ₗ⁅K⁆ LieDerivation K R R := (adoIdealAd R).comp C.incl
  have hT (z : C) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
    apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
      (adoExtendDerivation_mul (ψ z)) T
    intro a
    rw [adoExtendDerivation_ι]
    have hza : (ψ z a).1 ∈ N := by
      apply Submodule.mem_sup_left
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top z.1) a.2
    exact hgenN ⟨ψ z a, hza⟩
  have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
    intro z u hu
    change adoExtendDerivation (ψ z) u ∈ T ^ k
    exact adoUEA_derivation_preserves_idealPower
      (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
      T (hT z) k hu
  let B := k * (Module.finrank K V + 1)
  have hp (i : Fin (Module.finrank K R)) : (p i).Monic := by
    exact Polynomial.monic_X.mul (LinearMap.charpoly_monic (ρ₀ (b i)))
  have hdegree (i : Fin (Module.finrank K R)) : (p i ^ k).natDegree = B := by
    rw [(hp i).natDegree_pow]
    simp [p, B, V, LinearMap.charpoly_natDegree,
      (LinearMap.charpoly_monic (ρ₀ (b i))).ne_zero]
  have hpow (i : Fin (Module.finrank K R)) :
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B := by
    have hrelpow : Polynomial.aeval
        (UniversalEnvelopingAlgebra.ι K (b i)) (p i ^ k) ∈ Q := by
      rw [map_pow]
      exact Ideal.pow_mem_pow (hgenRel i) k
    have hm := adoAeval_monic_mem_modWords Q b i (p i ^ k)
      ((hp i).pow k) hrelpow
    rwa [hdegree i] at hm
  let qK := (Q : Submodule (adoUEA K R) (adoUEA K R)).restrictScalars K
  let _ : Module.Finite K (adoUEA K R ⧸ qK) :=
    adoQuotient_finite_of_power_relations Q b hpow
  let ρQ : (R ⋊⁅ψ⁆ C) →ₗ⁅K⁆ Module.End K (adoUEA K R ⧸ qK) :=
    adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
  let e : (R ⋊⁅ψ⁆ C) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl R C hc
  let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K R ⧸ qK) := ρQ.comp e.symm
  have hcenter : ∀ x : L, x ∈ LieAlgebra.center K L → ρL x = 0 → x = 0 := by
    intro x hx hxzero
    let r : R := ⟨x, LieAlgebra.center_le_radical K L hx⟩
    have her : e.symm x = (⟨r, 0⟩ : R ⋊⁅ψ⁆ C) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv x) = x := e.apply_symm_apply x
        _ = e.toLinearEquiv (⟨r, 0⟩ : R ⋊⁅ψ⁆ C) := by
          change x = r.1 + 0
          simp [r]
    have hr : r = 0 := by
      apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
      change ρQ ⟨r, 0⟩ = 0
      change ρQ (e.symm x) = 0 at hxzero
      rwa [her] at hxzero
    exact congrArg Subtype.val hr
  exact ado_transport_fin
    (adoDirectSum ρL (LieModule.toEnd K L L))
    (ado_faithful_of_faithful_on_center ρL hcenter)

end MathlibExt.Algebra.Lie.LandmarkWanted

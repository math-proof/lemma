import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.LinearCombination
import Structure.IharaLemma_IdempotentSplitting

namespace IharaLemma


namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)

theorem 𝔪_injective : Function.Injective S.𝔪 := by
  intro i j h
  by_contra hij
  have h1 : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr hij
  rw [← h] at h1
  exact ((S.mem_iff i i).mp h1) rfl

theorem notMem (i : Fin S.n) : S.e i ∉ S.𝔪 i := fun h => ((S.mem_iff i i).mp h) rfl

theorem mem_of_ne {i j : Fin S.n} (h : i ≠ j) : S.e i ∈ S.𝔪 j := (S.mem_iff i j).mpr h

theorem mem_of_isMaximal_of_ne (i : Fin S.n) (J : Ideal B) (hJ : J.IsMaximal) (hne : J ≠ S.𝔪 i) :
    S.e i ∈ J := by
  obtain ⟨j, rfl⟩ := S.exists_eq J hJ
  exact S.mem_of_ne fun h => hne (congrArg S.𝔪 h.symm)

theorem idem (i : Fin S.n) : IsIdempotentElem (S.e i) := S.coi.idem i


end IdempotentSplitting

section CornerModule

variable {B : Type} [CommRing B] {M : Type} [AddCommGroup M] [Module B M]

def cornerSubmodule (e : B) : Submodule B M := LinearMap.range (e • (LinearMap.id : M →ₗ[B] M))

def toCorner (e : B) : M →ₗ[B] cornerSubmodule (M := M) e :=
  LinearMap.rangeRestrict (e • (LinearMap.id : M →ₗ[B] M))

@[simp] theorem toCorner_apply (e : B) (v : M) :
    ((toCorner (M := M) e v : cornerSubmodule e) : M) = e • v := rfl

end CornerModule

theorem exists_mul_mul_eq_of_notMem {B : Type} [CommRing B] {e : B} (he : IsIdempotentElem e)
    (𝔪 : Ideal B) (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) {s : B} (hs : s ∉ 𝔪) :
    ∃ t : B, t * s * e = e := by
  have htop : Ideal.span {s} ⊔ Ideal.span {1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1e : 1 - e ∈ J := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hsJ : s ∈ J := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
    have hJ𝔪 : J ≠ 𝔪 := fun h => hs (h ▸ hsJ)
    have heJ : e ∈ J := hother J hJ hJ𝔪
    apply hJ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := J.add_mem heJ h1e
    rwa [add_sub_cancel] at this
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, ?_⟩
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  have key : t * s * e + u * ((1 - e) * e) = 1 * e := by
    have := congrArg (· * e) hab
    simpa only [add_mul, mul_assoc] using this
  rwa [h0, mul_zero, add_zero, one_mul] at key

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)

abbrev CornerRing : Type := (S.idem i).Corner


theorem coe_mk_cornerRing (x : B) (hx) : ((⟨x, hx⟩ : S.CornerRing i) : B) = x := rfl

@[ext] theorem ext_cornerRing {z w : S.CornerRing i} (h : (z : B) = w) : z = w := Subtype.ext h

theorem coe_one_cornerRing : ((1 : S.CornerRing i) : B) = S.e i := rfl

def toCornerRing : B →+* S.CornerRing i where
  toFun b := ⟨S.e i * b * S.e i, b, rfl⟩
  map_one' := Subtype.ext (by
    show S.e i * 1 * S.e i = S.e i
    rw [mul_one, (S.idem i).eq])
  map_mul' a b := Subtype.ext (by
    show S.e i * (a * b) * S.e i = S.e i * a * S.e i * (S.e i * b * S.e i)
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (-(a * b) * (S.e i * S.e i + S.e i)) * h2)
  map_zero' := Subtype.ext (by
    show S.e i * 0 * S.e i = 0
    rw [mul_zero, zero_mul])
  map_add' a b := Subtype.ext (by
    show S.e i * (a + b) * S.e i = S.e i * a * S.e i + S.e i * b * S.e i
    rw [mul_add, add_mul])

@[simp] theorem coe_toCornerRing (b : B) :
    ((S.toCornerRing i b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl

theorem e_mul_coe (z : S.CornerRing i) : S.e i * (z : B) = z := by
  obtain ⟨_, a, rfl⟩ := z
  show S.e i * (S.e i * a * S.e i) = S.e i * a * S.e i
  rw [← mul_assoc, ← mul_assoc, (S.idem i).eq]

theorem coe_mul_e (z : S.CornerRing i) : (z : B) * S.e i = z := by
  rw [mul_comm]; exact S.e_mul_coe i z

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]


theorem algebraMap_base_cornerRing_coe (r : 𝒪) :
    ((algebraMap 𝒪 (S.CornerRing i) r : S.CornerRing i) : B) = S.e i * algebraMap 𝒪 B r * S.e i :=
  rfl

end Base

theorem algebraMap_cornerRing_coe (b : B) :
    ((algebraMap B (S.CornerRing i) b : S.CornerRing i) : B) = S.e i * b * S.e i := rfl


section CornerModule

variable {M : Type} [AddCommGroup M] [Module B M]

theorem e_smul_coe (m : cornerSubmodule (M := M) (S.e i)) : S.e i • (m : M) = m := by
  obtain ⟨m0, hm0⟩ := m.2
  rw [← hm0]
  show S.e i • (S.e i • m0) = S.e i • m0
  rw [smul_smul, (S.idem i).eq]

theorem coe_smul_mem (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    (z : B) • (m : M) ∈ cornerSubmodule (M := M) (S.e i) :=
  ⟨(z : B) • (m : M), by
    show S.e i • ((z : B) • (m : M)) = (z : B) • (m : M)
    rw [smul_smul, S.e_mul_coe]⟩


theorem coe_zero_cornerRing : ((0 : S.CornerRing i) : B) = 0 := rfl

@[simp] theorem coe_cornerSmul (z : S.CornerRing i) (m : cornerSubmodule (M := M) (S.e i)) :
    ((z • m : cornerSubmodule (M := M) (S.e i)) : M) = (z : B) • (m : M) := rfl


end CornerModule

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

noncomputable def cornerRingLinearEquiv :
    S.CornerRing i ≃ₗ[𝒪] ↥(cornerSubmodule (M := B) (S.e i)) where
  toFun x := ⟨x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b * S.e i, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination hb⟩
  invFun x := ⟨x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hy
    exact ⟨y, by linear_combination y * (S.idem i).eq + hy⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext (by
    obtain ⟨b, hb⟩ := x.2
    show (S.e i * algebraMap 𝒪 B r * S.e i) * (x : B) = r • (x : B)
    rw [Algebra.smul_def]
    linear_combination (algebraMap 𝒪 B r * b * (S.e i * S.e i + S.e i)) * (S.idem i).eq
      + (algebraMap 𝒪 B r - S.e i * algebraMap 𝒪 B r * S.e i) * hb)

@[simp] theorem cornerRingLinearEquiv_apply (x : S.CornerRing i) :
    ((cornerRingLinearEquiv S i 𝒪 x : cornerSubmodule (M := B) (S.e i)) : B) = (x : B) := rfl

@[simp] theorem cornerRingLinearEquiv_symm_apply (x : cornerSubmodule (M := B) (S.e i)) :
    (((cornerRingLinearEquiv S i 𝒪).symm x : S.CornerRing i) : B) = (x : B) := rfl

end Base

section BaseModule

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module 𝒪 M] [IsScalarTower 𝒪 B M]


end BaseModule

end IdempotentSplitting

end IharaLemma

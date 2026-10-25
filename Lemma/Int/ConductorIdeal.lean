import Mathlib
import sympy.Basic
import Def.RingTheory.ConductorIdeal
open Subalgebra


namespace Subalgebra

/--
[mem_conductorIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma mem_conductorIdeal
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S}
  {s : S} :
-- imply
  s ∈ A.conductorIdeal ↔ ∀ t : S, s * t ∈ A :=
-- proof
  Iff.rfl

end Subalgebra

namespace Subalgebra

/--
[conductorIdeal_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_top
  [CommSemiring R] [CommSemiring S] [Algebra R S] :
-- imply
  (⊤ : Subalgebra R S).conductorIdeal = ⊤ := by
-- proof
  rw [Ideal.eq_top_iff_one, mem_conductorIdeal]
  intro t
  exact Algebra.mem_top

end Subalgebra

namespace Subalgebra

/--
[adjoin_conductorIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma adjoin_conductorIdeal
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [CommRing R'] [CommRing S'] [Algebra R' S']
  {x : S'} :
-- imply
  (Algebra.adjoin R' ({x} : Set S')).conductorIdeal = conductor R' x :=
-- proof
  Ideal.ext fun _ => Iff.rfl
end Subalgebra
namespace Subalgebra
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (T : Subalgebra R K)
variable [IsFractionRing R K]
variable [IsDomain R]

end Subalgebra

namespace Subalgebra

/--
[conductorIdeal_bot_ne_bot_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_bot_ne_bot_of_finite
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
  {T : Subalgebra R K} [Module.Finite R ↥T] :
-- imply
  (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ := by
-- proof
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := ↥T)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (s.map ⟨Subtype.val, Subtype.val_injective⟩)
  have hb0 : (b : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
  have hd0 : algebraMap R ↥T (b : R) ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    have hcongr : ((algebraMap R ↥T (b : R) : ↥T) : K) =
      ((algebraMap R ↥T (0 : R) : ↥T) : K) := by
      rw [h, map_zero]
    exact hcongr
  refine (Submodule.ne_bot_iff _).mpr ⟨algebraMap R ↥T (b : R), ?_, hd0⟩
  rw [Subalgebra.mem_conductorIdeal]
  intro t
  have ht : t ∈ Submodule.span R s := by rw [hs]; exact Submodule.mem_top
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp ht
  have key : ∀ x ∈ s, algebraMap R ↥T (b : R) * x ∈ (⊥ : Subalgebra R ↥T) := by
    intro x hx
    obtain ⟨r, hr⟩ :=
      RingHom.mem_rangeS.mp (hb (x : K) (Finset.mem_map.mpr ⟨x, hx, rfl⟩))
    have e1 : ((algebraMap R ↥T (b : R) * x : ↥T) : K)
      = algebraMap R K (b : R) * (x : K) := by simp
    have hval : ((algebraMap R ↥T (b : R) * x : ↥T) : K) = algebraMap R K r := by
      rw [e1, hr, Algebra.smul_def]
    have heq : algebraMap R ↥T (b : R) * x = algebraMap R ↥T r := Subtype.ext hval
    rw [heq]
    exact Algebra.mem_bot.mpr ⟨r, rfl⟩
  rw [← hf, Finset.mul_sum]
  exact sum_mem (fun x hx => by
    rw [Algebra.mul_smul_comm, Algebra.smul_def]
    exact (⊥ : Subalgebra R ↥T).mul_mem (Algebra.mem_bot.mpr ⟨_, rfl⟩) (key x hx))
variable [IsNoetherianRing R]

end Subalgebra

namespace Subalgebra

/--
[finite_of_conductorIdeal_bot_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma finite_of_conductorIdeal_bot_ne_bot
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K}
-- given
  (h : (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥) :
-- imply
  Module.Finite R ↥T := by
-- proof
  obtain ⟨c, hc_mem, hc0⟩ := (Submodule.ne_bot_iff _).mp h
  have hcK : ((c : ↥T) : K) ≠ 0 := by
    rintro h0
    exact hc0 (Subtype.ext h0)
  have hmul_inj : Function.Injective (fun t : ↥T => c * t) := by
    intro a b hab
    have h2 : ((c * a : ↥T) : K) = ((c * b : ↥T) : K) := congrArg _ hab
    have hK : ((c : ↥T) : K) * (a : K) = ((c : ↥T) : K) * (b : K) := by
      simpa using h2
    have habK : (a : K) = (b : K) := mul_left_cancel₀ hcK hK
    exact Subtype.ext habK
  let g₀ : ↥T →ₗ[R] ↥T :=
    { toFun := fun t => c * t
      map_add' := fun a b => mul_add _ _ _
      map_smul' := fun r x => Algebra.mul_smul_comm _ _ _ }
  let g : ↥T →ₗ[R] ↥(⊥ : Subalgebra R ↥T) :=
    g₀.codRestrict (⊥ : Subalgebra R ↥T).toSubmodule
      (fun t => Subalgebra.mem_conductorIdeal.mp hc_mem t)
  have hg_inj : Function.Injective g :=
    fun a b hab => hmul_inj (congrArg Subtype.val hab)
  have hfin : Module.Finite R ↥(⊥ : Subalgebra R ↥T) := inferInstance
  have hFG : (Submodule.map g ⊤).FG := Submodule.FG.of_le hfin.fg_top le_top
  have hTop : (⊤ : Submodule R ↥T).FG :=
    Submodule.fg_of_fg_map_injective g hg_inj hFG
  exact Module.Finite.of_fg_top hTop

end Subalgebra

namespace Subalgebra

/--
[bot_conductorIdeal_ne_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma bot_conductorIdeal_ne_bot_iff
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K} :
-- imply
  (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite R ↥T :=
-- proof
  ⟨finite_of_conductorIdeal_bot_ne_bot T,
    fun h => @conductorIdeal_bot_ne_bot_of_finite _ _ _ _ _ T _ _ h⟩

end Subalgebra

namespace Subalgebra

/--
[integralClosure_bot_conductorIdeal_ne_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma integralClosure_bot_conductorIdeal_ne_bot_iff
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R] [IsNoetherianRing R]
  {T : Subalgebra R K} :
-- imply
  (⊥ : Subalgebra R ↥(integralClosure R K)).conductorIdeal ≠ ⊥ ↔
    Module.Finite R ↥(integralClosure R K) :=
-- proof
  bot_conductorIdeal_ne_bot_iff (integralClosure R K)

end Subalgebra

/--
[le_conductorIdeal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma le_conductorIdeal_iff
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S}
  {I : Ideal S} :
-- imply
  I ≤ A.conductorIdeal ↔ (I : Set S) ⊆ (A : Set S) := by
-- proof
  constructor
  · intro h s hs
    have hmem := mem_conductorIdeal.mp (h hs)
    simpa using hmem 1
  · intro h s hs t
    exact h (I.mul_mem_right t hs)


namespace Subalgebra

/--
[conductorIdeal_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_subset
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S} :
-- imply
  (A.conductorIdeal : Set S) ⊆ (A : Set S) :=
-- proof
  le_conductorIdeal_iff.mp le_rfl

end Subalgebra

namespace Subalgebra

/--
[conductorIdeal_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_mono
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A B : Subalgebra R S}
-- given
  (h : A ≤ B) :
-- imply
  A.conductorIdeal ≤ B.conductorIdeal := by
-- proof
  intro s hs
  rw [mem_conductorIdeal] at hs ⊢
  exact fun t => h (hs t)

end Subalgebra

namespace Subalgebra

/--
[conductorIdeal_eq_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_eq_top_iff
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  {A : Subalgebra R S} :
-- imply
  A.conductorIdeal = ⊤ ↔ A = ⊤ := by
-- proof
  constructor
  · intro h
    rw [Algebra.eq_top_iff]
    intro x
    have hle : (⊤ : Ideal S) ≤ A.conductorIdeal := by rw [h]
    exact le_conductorIdeal_iff.mp hle trivial
  · rintro rfl
    exact conductorIdeal_top

end Subalgebra

namespace Subalgebra

/--
[conductorIdeal_comap_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean)
-/
@[path]
lemma conductorIdeal_comap_le
  [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]
  {f : S →ₐ[R] T}
  {B : Subalgebra R T} :
-- imply
  (B.conductorIdeal).comap f.toRingHom ≤ (B.comap f).conductorIdeal := by
-- proof
  intro x hx t
  rw [Subalgebra.mem_comap, map_mul]
  exact mem_conductorIdeal.mp (Ideal.mem_comap.mp hx) (f t)

end Subalgebra


-- created on 2026-10-20
-- updated on 2026-10-23

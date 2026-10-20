/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ConductorIdeal.lean -/

import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.Finiteness.Subalgebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Conductor ideal of a subalgebra

For a subalgebra `A` of a commutative `R`-algebra `S`, the conductor ideal of `A`
is the largest ideal of `S` contained in `A`: it consists of those `s : S` with
`s * t ∈ A` for every `t : S`. For `A = Algebra.adjoin R {x}` this recovers
Mathlib's element-generated conductor `conductor R x`.
-/

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Subalgebra

/-- The conductor ideal of a subalgebra `A`: the largest ideal of `S`
contained in `A`. -/
def conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {s : S | ∀ t : S, s * t ∈ A}
  zero_mem' t := by simp
  add_mem' ha hb t := by simpa only [add_mul] using A.add_mem (ha t) (hb t)
  smul_mem' c a ha t := by
    simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * t)

/-- Membership in the conductor ideal. -/
theorem mem_conductorIdeal {A : Subalgebra R S} {s : S} :
    s ∈ A.conductorIdeal ↔ ∀ t : S, s * t ∈ A :=
  Iff.rfl

/-- Universal property: an ideal lies in the conductor ideal of `A` if and only
if it lies in `A`. -/
theorem le_conductorIdeal_iff {A : Subalgebra R S} {I : Ideal S} :
    I ≤ A.conductorIdeal ↔ (I : Set S) ⊆ (A : Set S) := by
  constructor
  · intro h s hs
    have hmem := mem_conductorIdeal.mp (h hs)
    simpa using hmem 1
  · intro h s hs t
    exact h (I.mul_mem_right t hs)

/-- The conductor ideal is contained in the subalgebra. -/
theorem conductorIdeal_subset (A : Subalgebra R S) :
    (A.conductorIdeal : Set S) ⊆ (A : Set S) :=
  le_conductorIdeal_iff.mp le_rfl

/-- The conductor ideal is monotone in the subalgebra. -/
theorem conductorIdeal_mono {A B : Subalgebra R S} (h : A ≤ B) :
    A.conductorIdeal ≤ B.conductorIdeal := by
  intro s hs
  rw [mem_conductorIdeal] at hs ⊢
  exact fun t => h (hs t)

/-- The conductor ideal of the top subalgebra is the top ideal. -/
@[simp]
theorem conductorIdeal_top : (⊤ : Subalgebra R S).conductorIdeal = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_conductorIdeal]
  intro t
  exact Algebra.mem_top

/-- The conductor ideal is the top ideal if and only if the subalgebra is. -/
theorem conductorIdeal_eq_top_iff {A : Subalgebra R S} :
    A.conductorIdeal = ⊤ ↔ A = ⊤ := by
  constructor
  · intro h
    rw [Algebra.eq_top_iff]
    intro x
    have hle : (⊤ : Ideal S) ≤ A.conductorIdeal := by rw [h]
    exact le_conductorIdeal_iff.mp hle trivial
  · rintro rfl
    exact conductorIdeal_top

variable {T : Type*} [CommSemiring T] [Algebra R T]

/-- Comapping the conductor ideal along an algebra map lands in the conductor
ideal of the comapped subalgebra. -/
theorem conductorIdeal_comap_le (f : S →ₐ[R] T) (B : Subalgebra R T) :
    (B.conductorIdeal).comap f.toRingHom ≤ (B.comap f).conductorIdeal := by
  intro x hx t
  rw [Subalgebra.mem_comap, map_mul]
  exact mem_conductorIdeal.mp (Ideal.mem_comap.mp hx) (f t)

/-- For a monogenic subalgebra this recovers Mathlib's element-generated
conductor. -/
theorem adjoin_conductorIdeal {R' S' : Type*} [CommRing R'] [CommRing S']
    [Algebra R' S'] (x : S') :
    (Algebra.adjoin R' ({x} : Set S')).conductorIdeal = conductor R' x :=
  Ideal.ext fun _ => Iff.rfl

end Subalgebra

namespace Subalgebra

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] (T : Subalgebra R K)

variable [IsFractionRing R K]

variable [IsDomain R]

/-- A finite overring in the fraction field has nonzero conductor. -/
theorem conductorIdeal_bot_ne_bot_of_finite [Module.Finite R ↥T] :
    (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ := by
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

omit [IsFractionRing R K] [IsDomain R] in
/-- An overring in the fraction field with nonzero conductor is finite. -/
theorem finite_of_conductorIdeal_bot_ne_bot
    (h : (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥) : Module.Finite R ↥T := by
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

/-- Nonvanishing of the conductor of the bottom subalgebra characterizes
finiteness of an overring in the fraction field. -/
theorem bot_conductorIdeal_ne_bot_iff :
    (⊥ : Subalgebra R ↥T).conductorIdeal ≠ ⊥ ↔ Module.Finite R ↥T :=
  ⟨finite_of_conductorIdeal_bot_ne_bot T,
    fun h => @conductorIdeal_bot_ne_bot_of_finite _ _ _ _ _ T _ _ h⟩

/-- The finiteness characterization for the integral closure in the same
fraction field. -/
theorem integralClosure_bot_conductorIdeal_ne_bot_iff :
    (⊥ : Subalgebra R ↥(integralClosure R K)).conductorIdeal ≠ ⊥ ↔
      Module.Finite R ↥(integralClosure R K) :=
  bot_conductorIdeal_ne_bot_iff (integralClosure R K)

end Subalgebra

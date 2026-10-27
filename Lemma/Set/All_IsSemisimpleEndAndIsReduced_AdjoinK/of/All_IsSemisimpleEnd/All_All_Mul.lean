import Mathlib
import Initialize.Tactic.Attr.Basic


private lemma commute_of_mem_adjoin
  {K : Type*}
  [Field K]
  [PerfectField K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {s : Set (Module.End K V)} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
  {x y : Module.End K V} (hx : x ∈ Algebra.adjoin K s) (hy : y ∈ Algebra.adjoin K s) : Commute x y := by
  have h1 := Algebra.adjoin_le_centralizer_centralizer K s hx
  have h2 : y ∈ Subalgebra.centralizer K s := by
    refine (Algebra.adjoin_le (fun z hz => ?_) : Algebra.adjoin K s ≤ Subalgebra.centralizer K s) hy
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro w hw
    exact hcomm w hw z hz
  rw [Subalgebra.mem_centralizer_iff] at h1
  exact (h1 y h2).symm

private lemma isSemisimple_of_mem_adjoin
  {K : Type*}
  [Field K]
  [PerfectField K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {s : Set (Module.End K V)}
  (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x)
  {a : Module.End K V} (ha : a ∈ Algebra.adjoin K s) : a.IsSemisimple := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Module.End.IsSemisimple_smul r Module.End.isSemisimple_id
  | add x y hx hy ihx ihy => exact Module.End.IsSemisimple.add_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy
  | mul x y hx hy ihx ihy => exact Module.End.IsSemisimple.mul_of_commute (commute_of_mem_adjoin hcomm hx hy) ihx ihy

private lemma isReduced_adjoin
  {K : Type*}
  [Field K]
  [PerfectField K]
  {V : Type*}
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {s : Set (Module.End K V)}
  (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
  IsReduced (Algebra.adjoin K s) := by
  constructor
  rintro ⟨x, hx⟩ ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    have := congrArg Subtype.val hn
    simpa using this
  refine Subtype.ext
    (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨n, hxn⟩ (isSemisimple_of_mem_adjoin hcomm hs hx))
/--
[Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_forall_isSemisimple_and_isReduced_adjoin_of_commute.lean)
-/
@[path]
private lemma main
  [Field K] [PerfectField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {s : Set (Module.End K V)}
-- given
  (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x)
  (hs : ∀ x ∈ s, Module.End.IsSemisimple x) :
-- imply
  (∀ a ∈ Algebra.adjoin K s, Module.End.IsSemisimple a) ∧ IsReduced ↥(Algebra.adjoin K s) :=
-- proof
  ⟨fun _ ha => isSemisimple_of_mem_adjoin hcomm hs ha, isReduced_adjoin hcomm hs⟩


-- created on 2026-10-23

import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma forall_add_apply_eq_iff
  [CommRing R]
  [Fintype ι] [AddCommGroup ι]
  (f g : PrimeSpectrum R → ι)
  (e e' : ι → R)
  -- given
  (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
  (hge : ∀ (i : ι) (x : PrimeSpectrum R), g x = i ↔ e' i ∉ x.asIdeal) :
  -- imply
  ∀ (k : ι) (x : PrimeSpectrum R), f x + g x = k ↔ (∑ i, e i * e' (k - i)) ∉ x.asIdeal := by
  -- proof
  classical
  intro k x
  have hf : e (f x) ∉ x.asIdeal := (hfe _ x).mp rfl
  have hg : e' (g x) ∉ x.asIdeal := (hge _ x).mp rfl
  have hterm : ∀ i, i ≠ f x → e i * e' (k - i) ∈ x.asIdeal := by
    intro i hi
    apply x.asIdeal.mul_mem_right _ _
    ·
      by_contra h
      apply hi ((hfe i x).mpr h).symm
  have hsplit : (∑ i, e i * e' (k - i)) ∉ x.asIdeal ↔ e (f x) * e' (k - f x) ∉ x.asIdeal := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (f x))]
    have hrest : (∑ i ∈ Finset.univ.erase (f x), e i * e' (k - i)) ∈ x.asIdeal :=
      x.asIdeal.sum_mem fun i hi => hterm i (Finset.ne_of_mem_erase hi)
    constructor
    ·
      intro h hmain
      apply h (x.asIdeal.add_mem hmain hrest)
    ·
      intro h hsum
      apply h (by simpa using x.asIdeal.sub_mem hsum hrest)
  rw [hsplit]
  constructor
  ·
    intro hk
    rw [← hk, add_sub_cancel_left]
    intro hmem
    obtain h | h := x.isPrime.mem_or_mem hmem
    · apply hf h
    · apply hg h
  ·
    intro h
    have h2 : e' (k - f x) ∉ x.asIdeal := fun hm => h (x.asIdeal.mul_mem_left _ hm)
    have : g x = k - f x := (hge _ x).mpr h2
    rw [this, add_sub_cancel]

/--
[PrimeSpectrum_forall_sub_apply_eq_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PrimeSpectrum_forall_sub_apply_eq_iff.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [Fintype ι] [AddCommGroup ι]
  (f g : PrimeSpectrum R → ι)
  (e e' : ι → R)
  -- given
  (hfe : ∀ (i : ι) (x : PrimeSpectrum R), f x = i ↔ e i ∉ x.asIdeal)
  (hge : ∀ (i : ι) (x : PrimeSpectrum R), g x = i ↔ e' i ∉ x.asIdeal) :
  -- imply
  ∀ (k : ι) (x : PrimeSpectrum R), f x - g x = k ↔ (∑ i, e i * e' (i - k)) ∉ x.asIdeal := by
  -- proof
  have hneg : ∀ (i : ι) (x : PrimeSpectrum R), (-g x) = i ↔ e' (-i) ∉ x.asIdeal :=
    fun i x => by
      rw [← hge, neg_eq_iff_eq_neg]
  intro k x
  simpa only [← sub_eq_add_neg, neg_sub] using forall_add_apply_eq_iff f (fun x => -g x) e (fun i => e' (-i)) hfe hneg k x


-- created on 2026-10-20

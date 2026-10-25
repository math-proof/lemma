import Mathlib
import sympy.Basic
import Def.Dynamics.Preperiodic.Part2
open Function


namespace Function

/--
[mem_forwardOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma mem_forwardOrbit
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  y ∈ forwardOrbit f x ↔ ∃ n : ℕ, f^[n] x = y := by
-- proof
  simp [forwardOrbit]

end Function

namespace Function

/--
[isPreperiodicPt_iff_exists_eq_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma isPreperiodicPt_iff_exists_eq_iterate
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  IsPreperiodicPt f x ↔ ∃ m n : ℕ, m < n ∧ f^[m] x = f^[n] x := by
-- proof
  constructor
  · intro hfin
    have hinj : ¬Injective (fun n : ℕ => f^[n] x) := by
      intro hinj
      exact (Set.infinite_range_of_injective hinj) hfin
    obtain ⟨a, b, heq, hab⟩ := not_injective_iff.mp hinj
    by_cases h : a < b
    · exact ⟨a, b, h, heq⟩
    · exact ⟨b, a, by omega, heq.symm⟩
  · rintro ⟨m, n, hlt, heq⟩
    have hp : 0 < n - m := by omega
    have hperiodic : IsPeriodicPt f (n - m) (f^[m] x) := by
      rw [IsPeriodicPt]
      change f^[n - m] (f^[m] x) = f^[m] x
      rw [← iterate_add_apply]
      simpa [Nat.sub_add_cancel (Nat.le_of_lt hlt)] using heq.symm
    have hsub : forwardOrbit f x ⊆ Set.range (fun k : Fin n => f^[k.val] x) := by
      intro y hy
      rw [mem_forwardOrbit] at hy
      obtain ⟨k, rfl⟩ := hy
      by_cases hk : k < m
      · exact ⟨⟨k, hk.trans hlt⟩, rfl⟩
      · have hmk : m ≤ k := Nat.le_of_not_gt hk
        let t := k - m
        let r := t % (n - m)
        have hr : r < n - m := Nat.mod_lt _ hp
        refine ⟨⟨m + r, by omega⟩, ?_⟩
        calc
          f^[m + r] x = f^[r] (f^[m] x) := by
            rw [← iterate_add_apply]
            congr 1
            omega
          _ = f^[t] (f^[m] x) := hperiodic.iterate_mod_apply t
          _ = f^[m + t] x := by
            rw [← iterate_add_apply]
            congr 1
            omega
          _ = f^[k] x := by
            congr 1
            simp [t, Nat.add_sub_of_le hmk]
    exact (Set.finite_range _).subset hsub

end Function

namespace Function

/--
[isPreperiodicPtOfType_iff_isPeriodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma isPreperiodicPtOfType_iff_isPeriodicPt
  {f : α → α}
  {x y z : α}
  {m n : ℕ} :
-- imply
  IsPreperiodicPtOfType f m n x ↔ 0 < n ∧ IsPeriodicPt f n (f^[m] x) := by
-- proof
  constructor
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rw [IsPeriodicPt]
    change f^[n] (f^[m] x) = f^[m] x
    simpa only [← iterate_add_apply, Nat.add_comm] using h
  · rintro ⟨hn, h⟩
    refine ⟨hn, ?_⟩
    rw [IsPeriodicPt] at h
    change f^[n] (f^[m] x) = f^[m] x at h
    simpa only [← iterate_add_apply, Nat.add_comm] using h

end Function

namespace Function

/--
[grandOrbitRel_iff_inter_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma grandOrbitRel_iff_inter_nonempty
  {f : α → α}
  {x y z : α} :
-- imply
  GrandOrbitRel f x y ↔ (forwardOrbit f x ∩ forwardOrbit f y).Nonempty := by
-- proof
  constructor
  · rintro ⟨m, n, heq⟩
    exact ⟨f^[m] x, ⟨⟨m, rfl⟩, ⟨n, heq.symm⟩⟩⟩
  · rintro ⟨w, ⟨⟨m, hm⟩, ⟨n, hn⟩⟩⟩
    exact ⟨m, n, hm.trans hn.symm⟩

end Function

/--
[mem_forwardOrbit_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma mem_forwardOrbit_self
  {x y z : α}
  {f : α → α}
  {x : α} :
-- imply
  x ∈ forwardOrbit f x :=
-- proof
  ⟨0, by simp⟩


namespace Function

/--
[forwardOrbit_eq_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma forwardOrbit_eq_range
  {x y z : α}
  {m n : ℕ}
  {f : α → α}
  {x : α} :
-- imply
  forwardOrbit f x = Set.range (fun n : ℕ => f^[n] x) :=
-- proof
  rfl

end Function

namespace Function

/--
[isStrictlyPreperiodicPt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma isStrictlyPreperiodicPt_iff
  {f : α → α}
  {x y z : α} :
-- imply
  IsStrictlyPreperiodicPt f x ↔ IsPreperiodicPt f x ∧ x ∉ periodicPts f :=
-- proof
  Iff.rfl

end Function

namespace Function

/--
[IsPreperiodicPtOfType.isPreperiodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma IsPreperiodicPtOfType.isPreperiodicPt
  {f : α → α}
  {x y z : α}
  {m n : ℕ}
-- given
  (h : IsPreperiodicPtOfType f m n x) :
-- imply
  IsPreperiodicPt f x := by
-- proof
  rw [isPreperiodicPt_iff_exists_eq_iterate]
  exact ⟨m, m + n, Nat.lt_add_of_pos_right h.1, h.2.symm⟩

end Function

namespace Function

/--
[mem_grandOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
lemma mem_grandOrbit
  {f : α → α}
  {x y z : α} :
-- imply
  y ∈ grandOrbit f x ↔ GrandOrbitRel f x y :=
-- proof
  Iff.rfl

end Function

/--
[grandOrbitRel_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma grandOrbitRel_refl_eq
  {x y z : α}
  {f : α → α}
  {x : α} :
-- imply
  GrandOrbitRel f x x := by
-- proof
  apply Function.grandOrbitRel_refl f x

/--
[GrandOrbitRel.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma GrandOrbitRel_symm_eq
  {f : α → α}
  {x y z : α}
-- given
  (h : GrandOrbitRel f x y) :
-- imply
  GrandOrbitRel f y x := by
-- proof
  apply Function.GrandOrbitRel.symm h

/--
[GrandOrbitRel.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma GrandOrbitRel_trans_eq
  {f : α → α}
  {x y z : α}
-- given
  (hxy : GrandOrbitRel f x y)
  (hyz : GrandOrbitRel f y z) :
-- imply
  GrandOrbitRel f x z := by
-- proof
  apply Function.GrandOrbitRel.trans hxy hyz

/--
[grandOrbitRel_equivalence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean)
-/
@[path]
private lemma grandOrbitRel_equivalence_eq
  {f : α → α} :
-- imply
  Equivalence (GrandOrbitRel f) where
    refl := by
-- proof
  apply Function.grandOrbitRel_equivalence f


-- created on 2026-10-20
-- updated on 2026-10-23

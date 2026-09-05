import sympy.Basic
import sympy.sets.sets


@[main]
private lemma main
  {d : ℕ}
-- given
  (hd : d > 0)
  (n l u i : ℕ)
  (t : ℤ) :
-- imply
  let l' := i - l
  let u' := min (n - 1) (i + u)
  (i : ℤ) - l + (d : ℤ) * t ∈ Icc (l' : ℤ) (u' : ℤ) ↔ t ∈ Icc ⌈((l' : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌉ ⌊((u' : ℤ) - ((i : ℤ) - l)) / (d : ℚ)⌋ := by
-- proof
  intro l' u'
  simp [Set.mem_Icc]
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  constructor
  ·
    intro ⟨hl'j, hju'⟩
    constructor
    ·
      have h1 : ((l' : ℤ) - ((i : ℤ) - l)) ≤ t * (d : ℤ) := by linarith
      have h1' : ((l' : ℤ) - ((i : ℤ) - l) : ℚ) ≤ t * (d : ℚ) := by exact_mod_cast h1
      have h1'' : ((l' : ℤ) - ((i : ℤ) - l)) / (d : ℚ) ≤ t := by
        rw [div_le_iff₀ hd']
        linarith
      exact Int.ceil_le.mpr h1''
    ·
      have h2 : t * (d : ℤ) ≤ ((u' : ℤ) - ((i : ℤ) - l)) := by linarith
      have h2' : t * (d : ℚ) ≤ ((u' : ℤ) - ((i : ℤ) - l) : ℚ) := by exact_mod_cast h2
      have h2'' : t ≤ ((u' : ℤ) - ((i : ℤ) - l)) / (d : ℚ) := by
        rw [le_div_iff₀ hd']
        linarith
      exact Int.le_floor.mpr h2''
  ·
    intro ⟨htLo, htHi⟩
    constructor
    ·
      have h1 : ((l' : ℤ) - ((i : ℤ) - l) : ℚ) / (d : ℚ) ≤ t := Int.ceil_le.mp htLo
      have h1' : ((l' : ℤ) - ((i : ℤ) - l)) ≤ t * (d : ℤ) := by
        rw [div_le_iff₀ hd'] at h1
        exact_mod_cast h1
      linarith
    ·
      have h2 : t ≤ ((u' : ℤ) - ((i : ℤ) - l)) / (d : ℚ) := Int.le_floor.mp htHi
      have h2' : t * (d : ℤ) ≤ ((u' : ℤ) - ((i : ℤ) - l)) := by
        rw [le_div_iff₀ hd'] at h2
        exact_mod_cast h2
      linarith


-- created on 2026-07-28

import sympy.sets.sets
import sympy.Basic


@[main]
private lemma limits.merge
  {n : ℕ}
  {a b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ}
-- given
  (h : ∀ x ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin n → ℝ)), ∀ y ∈ Set.Icc a b, f (Fin.snoc (α := fun _ => ℝ) x y) > 0) :
-- imply
  ∀ z ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin (n + 1) → ℝ)), f z > 0 := by
-- proof
  intro z hz
  have hm := h (Fin.init z) (fun i _ => hz i.castSucc (Set.mem_univ _)) (z (Fin.last n)) (hz _ (Set.mem_univ _))
  rwa [Fin.snoc_init_self] at hm


@[main]
private lemma limits.split
  {n : ℕ}
  {a b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ}
-- given
  (h : ∀ z ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin (n + 1) → ℝ)), f z > 0) :
-- imply
  ∀ x ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin n → ℝ)), ∀ y ∈ Set.Icc a b, f (Fin.snoc (α := fun _ => ℝ) x y) > 0 := by
-- proof
  intro x hx y hy
  apply h
  intro i _
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hy
  · simpa using hx j (Set.mem_univ _)


@[main]
private lemma limits.merge.given
  {n : ℕ}
  {a b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ}
-- given
  (h : ∀ z ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin (n + 1) → ℝ)), f z > 0) :
-- imply
  ∀ x ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin n → ℝ)), ∀ y ∈ Set.Icc a b, f (Fin.snoc (α := fun _ => ℝ) x y) > 0 := by
-- proof
  intro x hx y hy
  apply h
  intro i _
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hy
  · simpa using hx j (Set.mem_univ _)


@[main]
private lemma limits.split.given
  {n : ℕ}
  {a b : ℝ}
  {f : (Fin (n + 1) → ℝ) → ℝ}
-- given
  (h : ∀ x ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin n → ℝ)), ∀ y ∈ Set.Icc a b, f (Fin.snoc (α := fun _ => ℝ) x y) > 0) :
-- imply
  ∀ z ∈ (Set.univ.pi (fun _ => Set.Icc a b) : Set (Fin (n + 1) → ℝ)), f z > 0 := by
-- proof
  intro z hz
  have hm := h (Fin.init z) (fun i _ => hz i.castSucc (Set.mem_univ _)) (z (Fin.last n)) (hz _ (Set.mem_univ _))
  rwa [Fin.snoc_init_self] at hm


-- created on 2026-09-27

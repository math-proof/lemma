import sympy.series.limits
open Finset

-- tests
variable (x : ℝ*) (r : ℝ) (x₀ : ℝ)
variable (f : ℕ → ℝ) (g : ℤ → ℝ) (h : ℝ → ℝ)

/--
info: (x - ↑r → 0) : Prop
-/
#guard_msgs in
#check (x - r) → 0

/--
info: ((x - ↑r) → ∞) : Prop
-/
#guard_msgs in
#check (x - r) → ∞

/--
info: (Hyperreal.omega - 1) → +∞ : Prop
-/
#guard_msgs in
#check (Hyperreal.omega - 1) → +∞

/--
info: (x - ↑r) → +∞ : Prop
-/
#guard_msgs in
#check (x - r) → +∞

/--
info: (Hyperreal.omega - 1) → -∞ : Prop
-/
#guard_msgs in
#check (Hyperreal.omega - 1) → -∞

/--
info: (x - ↑r) → -∞ : Prop
-/
#guard_msgs in
#check (x - r) → -∞

/--
info: Hyperreal.epsilon - 0 → 0⁺ : Prop
-/
#guard_msgs in
#check (Hyperreal.epsilon - 0) → 0⁺

/--
info: x - ↑r → 0⁺ : Prop
-/
#guard_msgs in
#check (x - r) → 0⁺

/--
info: Hyperreal.epsilon - 0 → 0⁻ : Prop
-/
#guard_msgs in
#check (Hyperreal.epsilon - 0) → 0⁻

/--
info: x - ↑r → 0⁻ : Prop
-/
#guard_msgs in
#check (x - r) → 0⁻

example : (lim [n → ∞] f n) = Filter.limUnder Filter.atTop fun n => f n :=
  rfl

example : (lim [n → ∞] g n) = Filter.limUnder Filter.atTop fun n => g n :=
  rfl

example : (lim [x → ∞] h x) = Filter.limUnder Filter.atTop fun x => h x :=
  rfl

example : (lim [(x : ℝ) → ∞] h x) = Filter.limUnder Filter.atTop fun x : ℝ => h x :=
  rfl

example : (lim [n → -∞] g n) = Filter.limUnder Filter.atBot fun n => g n :=
  rfl

example : (lim [x → -∞] h x) = Filter.limUnder Filter.atBot fun x => h x :=
  rfl

example : (lim [(n : ℤ) → -∞] g n) = Filter.limUnder Filter.atBot fun n : ℤ => g n :=
  rfl

example : (lim [x → 0] h x) = Filter.limUnder (nhdsWithin 0 {0}ᶜ) fun x => h x :=
  rfl

example : (lim [x → x₀] h x) = Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) fun x => h x :=
  rfl

example : (lim [(x : ℝ) → x₀] h x) = Filter.limUnder (nhdsWithin x₀ {x₀}ᶜ) fun x : ℝ => h x :=
  rfl

example : (lim [(x : ℝ) → 0] h x) = Filter.limUnder (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) fun x : ℝ => h x :=
  rfl

example : (lim [(x : ℝ) → 0⁺] h x) = Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) fun x : ℝ => h x :=
  rfl

example : (lim [(x : ℝ) → 0⁻] h x) = Filter.limUnder (nhdsWithin (0 : ℝ) (Set.Iio (0 : ℝ))) fun x : ℝ => h x :=
  rfl

example : (lim [x → 0⁺] h x) = Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) fun x => h x :=
  rfl

example : (lim [x → 0⁻] h x) = Filter.limUnder (nhdsWithin 0 (Set.Iio 0)) fun x => h x :=
  rfl

example : (lim [x → x₀⁺] h x) = Filter.limUnder (nhdsWithin x₀ (Set.Ioi x₀)) fun x => h x :=
  rfl

example : (lim [x → x₀⁻] h x) = Filter.limUnder (nhdsWithin x₀ (Set.Iio x₀)) fun x => h x :=
  rfl

example : (lim [(x : ℝ) → x₀⁺] h x) = Filter.limUnder (nhdsWithin x₀ (Set.Ioi x₀)) fun x : ℝ => h x :=
  rfl

example : (lim [(x : ℝ) → x₀⁻] h x) = Filter.limUnder (nhdsWithin x₀ (Set.Iio x₀)) fun x : ℝ => h x :=
  rfl

variable (a : ℝ)

example : lim [n → ∞] f n = a ↔ Filter.Tendsto (fun n => f n) Filter.atTop (nhds a) :=
  Iff.rfl

example : lim [x → ∞] h x = a ↔ Filter.Tendsto (fun x => h x) Filter.atTop (nhds a) :=
  Iff.rfl

example : lim [n → -∞] g n = a ↔ Filter.Tendsto (fun n => g n) Filter.atBot (nhds a) :=
  Iff.rfl

example : lim [x → 0] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin 0 {0}ᶜ) (nhds a) :=
  Iff.rfl

example : lim [x → x₀] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin x₀ {x₀}ᶜ) (nhds a) :=
  Iff.rfl

example : lim [(x : ℝ) → x₀] h x = a ↔
    Filter.Tendsto (fun x : ℝ => h x) (nhdsWithin x₀ {x₀}ᶜ) (nhds a) :=
  Iff.rfl

example : lim [x → 0⁺] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin 0 (Set.Ioi 0)) (nhds a) :=
  Iff.rfl

example : lim [x → 0⁻] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin 0 (Set.Iio 0)) (nhds a) :=
  Iff.rfl

example : lim [x → x₀⁺] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin x₀ (Set.Ioi x₀)) (nhds a) :=
  Iff.rfl

example : lim [x → x₀⁻] h x = a ↔ Filter.Tendsto (fun x => h x) (nhdsWithin x₀ (Set.Iio x₀)) (nhds a) :=
  Iff.rfl

/--
info: lim [n → ∞] f n : ℝ
-/
#guard_msgs in
#check lim [n → ∞] f n

/--
info: lim [n → -∞] g n : ℝ
-/
#guard_msgs in
#check lim [n → -∞] g n

/--
info: lim [x → 0] h x : ℝ
-/
#guard_msgs in
#check lim [x → 0] h x

/--
info: lim [x → x₀] h x : ℝ
-/
#guard_msgs in
#check lim [x → x₀] h x

/--
info: lim [x → 0⁺] h x : ℝ
-/
#guard_msgs in
#check lim [x → 0⁺] h x

/--
info: lim [x → 0⁻] h x : ℝ
-/
#guard_msgs in
#check lim [x → 0⁻] h x

/--
info: lim [x → x₀⁺] h x : ℝ
-/
#guard_msgs in
#check lim [x → x₀⁺] h x

/--
info: lim [x → x₀⁻] h x : ℝ
-/
#guard_msgs in
#check lim [x → x₀⁻] h x

/--
info: lim [x → x₀] h x = a : Prop
-/
#guard_msgs in
#check lim [x → x₀] h x = a

/--
info: lim [x → x₀⁺] h x = a : Prop
-/
#guard_msgs in
#check lim [x → x₀⁺] h x = a

/--
info: lim [x → x₀⁻] h x = a : Prop
-/
#guard_msgs in
#check lim [x → x₀⁻] h x = a

/--
info: lim [x → 0] h x = a : Prop
-/
#guard_msgs in
#check lim [x → 0] h x = a

/--
info: lim [n → ∞] f n = a : Prop
-/
#guard_msgs in
#check lim [n → ∞] f n = a

#check lim [n → ∞] g n
#check lim [x → ∞] h x
#check lim [x → -∞] h x
#check lim [N → ∞] ∑ n ∈ range N, f n

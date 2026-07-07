import sympy.series.limits

-- tests
variable (x : ℝ*) (r : ℝ)
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

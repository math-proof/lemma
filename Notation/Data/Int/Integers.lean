module

public import Mathlib.Tactic

public section

export Int (fract sign)


notation:max n "is" "even" => Even n

notation:max n "isn't" "even" => ¬Even n

notation:max n "is" "odd" => Odd n

notation:max n "isn't" "odd" => ¬Odd n

infixl:70 "//" => Int.fdiv


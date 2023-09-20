/-
Following the exercises from `The Natural Number Game`:
https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/
-/

import Mathlib 

set_option autoImplicit false 

namespace Tutorial

open Nat (succ)

/- The `rfl` tactic closes a goal of the of form `x = x`. -/
example (x y z : ℕ) : x * y + z = x * y + z := by 
  rfl 

/- Given `h : x = y`, `rewrite [h]` rewrites `x` into `y` into the goal. -/
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by 
  rewrite [h]
  rfl 

/- You can also use `rw`, which automatically tries `rfl` afterwards. -/
example (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by 
  rw [h]

example (a b : ℕ) (h : succ a = b) : succ (succ a) = succ b := sorry 




/-        **Addition**            -/

-- You right-click on `Nat.add` and go to its definition in the standard library.
#check Nat.add

lemma add_zero (a : ℕ) : a + 0 = a := sorry 

lemma add_succ (a d : ℕ) : a + succ d = succ (a + d) := sorry 

lemma add_succ_zero (a : ℕ) : a + succ 0 = succ a := sorry 

/-
  The following needs to be proved by induction, 
  which is performed using the `induction` tactic.
-/
lemma zero_add (n : ℕ) : 0 + n = n := by 
  induction n with 
  | zero => rfl 
  | succ n' ih => 
    rewrite [add_succ, ih] -- you can do multiple rewrites at a time
    rfl


lemma add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := sorry 

lemma succ_add (a b : ℕ) : succ a + b = succ (a + b) := sorry 

lemma add_comm (a b : ℕ) : a + b = b + a := sorry 

lemma one_eq_succ_zero : 1 = succ 0 := sorry 

lemma succ_eq_add_one (n : ℕ) : succ n = n + 1 := sorry  

lemma add_right_comm (a b c : ℕ) : a + b + c = a + c + b := sorry 


/-      **Multiplication**         -/

#check Nat.mul

lemma mul_zero (m : ℕ) : 0 * m = 0 := sorry 

lemma mul_one (m : ℕ) : m * 1 = m := sorry 

lemma one_mul (m : ℕ): 1 * m = m := sorry 

lemma mul_add (t a b : ℕ) : t * (a + b) = t * a + t * b := sorry 

lemma mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := sorry 

lemma succ_mul (a b : ℕ) : succ a * b = a * b + b := sorry 

lemma add_mul (a b t : ℕ) : (a + b) * t = a * t + b * t := sorry 

lemma mul_comm (a b : ℕ) : a * b = b * a := sorry 

lemma mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := sorry 









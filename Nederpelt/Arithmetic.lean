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

example (a b : ℕ) (h : succ a = b) : succ (succ a) = succ b := by
  rw [h]

/-        **Addition**            -/

-- You right-click on `Nat.add` and go to its definition in the standard library.
#check Nat.add

lemma add_zero (a : ℕ) : a + 0 = a := by rfl

lemma add_succ (a d : ℕ) : a + succ d = succ (a + d) := by rfl

lemma add_succ_zero (a : ℕ) : a + succ 0 = succ a := by rfl

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


lemma add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ c' IHc =>
    repeat rw [add_succ]
    rw [IHc]

lemma succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b' IHb =>
    rw [add_succ, add_succ, IHb]

lemma add_comm (a b : ℕ) : a + b = b + a := by
  induction b with
  | zero => rw [add_zero, zero_add]
  | succ b' IHb =>
    rw [add_succ, IHb, succ_add]

lemma one_eq_succ_zero : 1 = succ 0 := by rfl

lemma succ_eq_add_one (n : ℕ) : succ n = n + 1 := by rfl

lemma add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, <- add_assoc]

/-      **Multiplication**         -/

#check Nat.mul

lemma mul_zero (a : ℕ) : a * 0 = 0 := by rfl

lemma mul_succ (a d : ℕ) : a * succ d = a * d + a := by rfl

lemma mul_succ_zero (a : ℕ) : a * succ 0 = a := by
  rw [mul_succ, mul_zero, zero_add]

lemma zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero => rfl
  | succ m' IHm => rw [mul_succ, IHm]

lemma mul_one (m : ℕ) : m * 1 = m := by
  apply mul_succ_zero 

lemma one_mul (m : ℕ): 1 * m = m := by
  induction m with
  | zero => rfl
  | succ m' IHm => rw [mul_succ, IHm]

lemma mul_add (t a b : ℕ) : t * (a + b) = t * a + t * b := by
  induction b with
  | zero => simp
  | succ b' IHb =>
    rw [add_succ, mul_succ, mul_succ, IHb, add_assoc]

lemma mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => repeat rw [mul_zero]
  | succ b' IHb =>
    rw [mul_succ, mul_succ, mul_add, IHb]

lemma succ_mul (a b : ℕ) : succ a * b = a * b + b := by
  induction b with
  | zero => rw [mul_zero, mul_zero]
  | succ b' IHb =>
    rewrite [mul_succ, mul_succ, IHb]
    rewrite [add_assoc, add_assoc, add_comm b', succ_add]
    rfl

lemma add_mul (a b t : ℕ) : (a + b) * t = a * t + b * t := by
  induction t with
  | zero => repeat rw [mul_zero]
  | succ t' IHt =>
    repeat rewrite [mul_succ]
    rewrite [IHt]
    repeat rewrite [add_assoc]
    rw [add_comm a (b * t' + b), add_assoc, add_comm a b]

lemma mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with
  | zero => rw [mul_zero, zero_mul]
  | succ b' IHb => rw [mul_succ, succ_mul, IHb]

lemma mul_left_comm (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm b (a * c), mul_assoc, mul_comm b c]









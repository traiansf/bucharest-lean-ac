import Mathlib

set_option autoImplicit false 

namespace Tutorial

section Propositional

variable (p q r : Prop)

/-
  `intros` and `exact`

  Given an implication `p₁ → p₂` as a goal,
  the `intros` tactic will assume the premise of the implication
  as a local hypothesis, and ask you to prove its conclusion. 

  The `exact` tactic accepts a term,
  and closes the goal if the type of that term
  is the same as the goal.
-/
example : p → q → p := by 
  intros hp 
  intros hq 
  exact hp

/-
  You can `intros` several hypotheses at a time.
-/
example : p → q → p := by 
  intros hp hq 
  exact hp 

/-
  The `assumption` closes the goal if any of the local hypotheses match exactly the goal 
-/
example : p → q → p := by 
  intros hp hq 
  assumption

/-
  `exact` accepts any term, not just a local hypothesis.
-/
example : p → (p → q) → q := by 
  intros hp hpq 
  -- recall that an implication is just a function, 
  -- so we can apply `hpq` on `hp` to get something of type `q`.
  exact (hpq hp)

lemma imp_trans : (p → q) → (p → r) → (p → r) := sorry 

/-
You can use the `#print` command to see the definition of a constant.
As you see, `Not p` is defined as `p → False`.
The notation `¬p` can be used for it.
-/
#print Not 

lemma dni : p → ¬¬p := sorry 

lemma contraposition : (p → q) → (¬q → ¬p) := sorry 

/-
  Beyond implication and negation, 
  the other propositional constructs, `False`, `And`, `Or` are defined inductively. 

  As such they have "introduction and elimination" principles which are analogous 
  to the natural deduction rules, and that simply follow from the type theory of Lean.
-/

/- You can use the `#check` command to see the type of a term -/
#check False.elim
example : False → q := by 
  intros h_false 
  exact (False.elim h_false)

/- The `apply` tactic lets you work on a goal backwards
   Given a goal of the form `p₂` and `h : p₁ → p₂`,
   `apply h` will transform the goal into `p₁`. 
-/
example : False → q := by 
  intros h_false 
  apply False.elim 
  assumption

example : p → ¬p → q := sorry 
  
/-
  `And` has two eliminators and an introduction principle.
-/
#check And.left
#check And.right
#check And.intro

example : p ∧ q → p := by
  intros hpq 
  exact (And.left hpq) -- `And.left hpq` can also be written as `hpq.left`

example : p → q → p ∧ q := by 
  intros hp hq 
  exact (And.intro hp hq)

lemma and_comm : p ∧ q → q ∧ p := sorry 

/-
  The `rcases` tactic performs the deconstruction of a hypothesis of an induction type
  For example, it can be used to split a conjunction.
-/
example : p ∧ (q ∧ r) → r := by 
  intros h 
  rcases h with ⟨hp, hq, hr⟩
  assumption

lemma and_assoc : p ∧ (q ∧ r) → (p ∧ q) ∧ r := sorry  

/-
  `Or` is dual to `And`. It has two constructors and one eliminator.
-/
#check Or.inl 
#check Or.inr 
#check Or.elim

/- `rcases` works for `Or` too, but in this case, it will split the proof in two 
   and ask you to prove the goal under each of the assumptions.
-/
example : (p ∨ q) → (q ∨ p) := by 
  intros h 
  rcases h with hp | hq
  -- The proof has to goals now. You enter them using `.`. 
  -- Be aware of the indentation! 
  . apply Or.inr 
    assumption
  . apply Or.inl 
    assumption

lemma or_of_and : (p ∧ q) → (p ∨ q) := sorry 

lemma or_assoc : p ∨ (q ∨ r) → (p ∨ q) ∨ r := sorry  

/-
  To prove an equivalence, you just need to prove both implications,
  as witnessed by `Iff.intro`
-/
example : (p → q → r) ↔ (p ∧ q → r) := sorry 

/-
  Lean is by default classical. 
  The law of excludded middle is a theorem in the standard library.
-/
#check Classical.em
/-
  You can use `by_cases h : p` tactic to split the proof 
  into the case when `p` holds, and the case `¬p` holds.
-/
lemma dn : ¬¬p ↔ p := sorry 

lemma contraposition' : (¬q → ¬p) → (p → q) := sorry 

end Propositional




section FirstOrder

-- We assume `α` to be a nonempty type and `p`, `q` be two predicates on `α`.
variable {α : Type} [Inhabited α] (p : α → Prop) (q : α → Prop) 

/- Introducing a universal goal can be done again with `intros`, just like for implication. 
   After all, `→` is just a particular case of `∀`.
-/
example : (∀ x, p x ∧ q x → p x) := by 
  intros a 
  exact And.left 

/- A `∀` is just a (dependent) function type, so a universal hypothesis 
  `h : ∀ x : α, p x` can simply be applied to an `a : α` to yield 
  `h a : p a`.
-/
example (a : α) : (∀ x, p x) → p a := by 
  intros h 
  exact (h a)

/- Alternatively, `specialize h a` will instantiate the universal `h` with `a`. -/
example (a : α) : (∀ x, p x ∧ q x) → p a := by 
  intros h 
  specialize h a
  exact h.left

lemma forall_imp : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry 

lemma forall_and : ((∀ x, p x) ∧ (∀ x, q x)) ↔ (∀ x, p x ∧ q x) := sorry  

/-
  A proof of `∃ x : α, p x` is (dependent) pair made 
  of a `w : α` (called the witness) and a proof that `w` satisfies `p w`.
-/
#check Exists.intro 
example : (∀ x, p x) → (∃ x, p x) := by 
  intros h 
  let w : α := default -- we pick an arbitrary term of `α` as the witness.
  exact Exists.intro w (h w)

/-
  Alternatively, the `use` tactic lets us give the witness
  and then instantiates the goal into proving that the chosen witness is indeed a witness.
-/
example : (∀ x, p x) → (∃ x, p x) := by 
  intros h 
  let w : α := default -- we pick an arbitrary term of `α` as the witness.
  use w 
  exact h w

lemma not_exists : (¬ ∃ x, p x) → ∀ x, ¬p x := sorry 

/- `∃` is an inductive, so you can use `rcases` on it, as before -/
lemma exists_not : (∃ x, ¬ p x) → ¬∀ x, p x := sorry 

/-
  The following is intuitionistically false. 
  You might want to use the `by_contra` tactic,
  which, in order to prove `p`, will ask you to prove `False`
  from the hypothesis `¬p`.
-/

lemma not_forall_not : (¬∀ x, ¬ p x) → (∃ x, p x) := sorry
  

end FirstOrder



import Mathlib

set_option autoImplicit false 

inductive Ty where 
| arrow : Ty → Ty → Ty 
| base : Ty 
deriving DecidableEq 

infixr:50 " ↣ " => Ty.arrow

abbrev Var := String 

inductive Term where 
| app : Term → Term → Term 
| lam : Var → Ty → Term → Term 
| var : Var → Term 
deriving DecidableEq 

instance : Coe Var Term where coe := Term.var

abbrev Context := Var → Option Ty 

def Context.update (Γ : Context) (key : Var) (val : Ty) :=
  fun x => if x = key then some val else Γ x 

inductive TypeOf : Context → Term → Ty → Prop where 
| var {Γ} {x : Var} {σ : Ty} : Γ x = some σ → TypeOf Γ (.var x) σ
| app {Γ} {t u : Term} {σ τ : Ty} : TypeOf Γ t (.arrow σ τ) → TypeOf Γ u σ → TypeOf Γ (.app t u) τ
| lam {Γ} {x : Var} {σ : Ty} {t : Term} {τ : Ty} : TypeOf (Γ.update x τ) t σ → TypeOf Γ (.lam x τ t) (.arrow τ σ)


def typeOf (Γ : Context) (t : Term) : Option Ty :=
  match t with 
  | .var x => Γ x
  | .app t u => 
    match typeOf Γ t with 
    | .some (.arrow σ τ) => 
      if σ = typeOf Γ u then τ 
      else none 
    | _ => none 
  | .lam _ σ t => 
    match typeOf Γ t with 
    | .some τ => some <| .arrow σ τ 
    | _ => none  

-- lemma typeof_var_update : 
--   TypeOf (Γ.update x σ) (.var x) σ

@[simp]
def rename (t : Term) (old new : Var) : Term :=
  match t with 
  | .var x => if x = old then .var new else .var x  
  | .app t u => .app (rename t old new) (rename u old new)
  | t@(.lam x σ u) => if x = old then t else .lam x σ (rename u old new) 

@[simp]
def rebind (t : Term) (old new : Var) : Term := 
  match t with 
  | .var x => if x = old then .var new else .var x  
  | .app t u => .app (rename t old new) (rename u old new)
  | t@(.lam x σ u) => if old = x then .lam new σ (rename u old new) else t 

@[simp]
def freeVars (t : Term) : Finset Var := 
  match t with 
  | .var x => {x}
  | .app t u => freeVars t ∪ freeVars u 
  | .lam x _ t => freeVars t |>.erase x

@[simp]
def isFreeVar (t : Term) (x : Var) : Prop := 
  match t with 
  | .var y => x = y 
  | .app t u => isFreeVar t x ∨ isFreeVar u x 
  | .lam y _ t => isFreeVar t x ∧ x ≠ y


@[simp]
def fresh (t : Term) (x : Var) : Prop := 
  match t with 
  | .var y => x ≠ y 
  | .app t u => fresh t x ∧ fresh u x
  | .lam y _ t => x ≠ y ∧ fresh t x 

lemma erase_singleton_neq {x y : Var} (h : y ≠ x) : [x].erase y = [x] := by 
  simp [h.symm]


-- example {l : List String} (x : String) : (l.remove x |>.remove x) = (l.remove x) := by 
--   have : x ∉ l.remove x := List.mem_remove_iff

#check Finset
example (s : Finset String) (x y : String) (h : x ≠ y) : (Finset.erase (insert x s) y) = (insert x (Finset.erase s y)) := by 
  exact Finset.erase_insert_of_ne h

example (s : Finset String) (x y : String) (h : x ≠ y) : (Finset.erase (insert x s) y) = (insert x (Finset.erase s y)) := by 
  exact Finset.erase_insert_of_ne h

example (s t : Finset String) (x : String) : Finset.erase (s ∪ t) x = s.erase x ∪ t.erase x := by 
  exact?

-- example {t : Term} {x y : Var} : x 

lemma rename_of_not_fv {t : Term} {x y : Var} : x ∉ freeVars t → rename t x y = t := by 
  intros nfv 
  induction t with 
  | var z => 
    simp at nfv ⊢ 
    exact fun h => False.elim <| nfv h.symm 
  | lam z _ t ih => 
    simp at nfv ⊢ 
    intros h ; push_neg at h <;> symm at h 
    exact ih (nfv h)
  | app u v ihu hv => 
    simp at nfv ⊢ 
    aesop? 


lemma fv_rename {t : Term} {x y : Var} : x ∈ freeVars t → fresh t y → freeVars (rename t x y) = (insert y (freeVars t |>.erase x)) := by 
  induction t with 
  | var z => 
    by_cases h : x = z 
    . simp [*]
    . intros h  
      simp? at h <;> contradiction 
  | lam z σ u ih => 
    intros fv nfv 
    simp at fv 
    rcases fv with ⟨hxz, fv⟩
    specialize ih fv 
    push_neg at hxz <;> symm at hxz 
    simp at nfv 
    have : x ≠ y := by 
      -- sorry -- because fresh u y contradicts x ∈ freeVars u 
      intros h 
      rw [h] at fv 
      sorry 
    specialize ih nfv.2 
    simp [*]
    have := Finset.erase_insert_of_ne (s := freeVars u) nfv.1
    rw [Finset.erase_insert_of_ne nfv.1]
    rw [Finset.erase_right_comm]
  | app u v ihu ihv => 
    intros fv nfv 
    simp at fv nfv 
    rcases fv with fv | fv 
    . specialize ihu fv nfv.1 
      by_cases h : x ∈ freeVars v 
      . specialize ihv h nfv.2 
        simp [*]
        rw [Finset.erase_union_distrib _ _ _]
      . simp [*]
        have : rename v x y = v := rename_of_not_fv h
        rw [this]
        rw [Finset.erase_union_distrib _ _ _]
        simp [*]
    . sorry -- the same as before


example {t u : Term} {σ : Ty} {x y : Var} : y ∉ freeVars t → freeVars (.lam x σ t) ⊆ freeVars (.lam y σ (rename t x y)) := by 
  intros nfv 
  intros a 

example (s : Finset String) (x : String) : (Finset.erase (insert x s) x) = s := by 
  have : x ∉ s := sorry 
  exact?

#check Finset.erase_right_comm
example {t u : Term} {σ : Ty} {x y : Var} : fresh t y → freeVars (.lam x σ t) = freeVars (.lam y σ (rename t x y)) := by 
  intros hfresh 
  by_cases h : x ∈ freeVars t 
  . 
    simp 
    rw [fv_rename h hfresh]
    have : y ∉ Finset.erase (freeVars t) x := sorry 
    rw [Finset.erase_insert this]
  . have : rename t x y = t := rename_of_not_fv h 
    rw [this]
    simp 
    sorry --neither x and y are in FV(t), so its ok 
  
  -- intros nfv 
  -- induction t with 
  -- | var z => 
  --   by_cases h' : z = x 
  --   . simp [*]
  --   . 
  --     simp? at nfv
  --     -- simp only [freeVars, List.mem_singleton] at nfv  
  --     have : x ≠ z := by exact Iff.mp ne_comm h'
  --     simp [*]
  -- | lam z τ v ih => 
  --   simp only [freeVars]
  --   by_cases h : x = z 
  --   . rw [h]
  --     simp [rename]
  --     simp at nfv 
  --     by_cases h' : y = z 
  --     . simp [h']
  --     . specialize nfv h' 
  --       simp [*]
  --   . simp [*]
  --     push_neg at h
  --     symm at h 
  --     simp [*]
  --     simp at nfv 
  --     by_cases h' : y = z 
  --     . rw [h']
  --       simp 

  --     . specialize nfv h' 
  --       -- ext a 
  --       -- simp 
  --       specialize ih nfv 
  --       simp at ih 
  --       rw [Finset.erase_right_comm]
  --       rw [ih]
  --       nth_rewrite 1 [Finset.erase_right_comm]
  --       rfl

-- lemma typeof_rename {Γ : Context} {t : Term} {x y : Var} :
--   Γ x = Γ y → typeOf Γ t = typeOf Γ (rename t x y) := by 
--   intros h 
--   induction t with 
--   | lam z σ u ih => 
--     by_cases h : z = x 
--     . simp [*]
--     . simp [*, typeOf]
--   | var z => 
--     by_cases h' : z = x 
--     . simp [*, typeOf]
--     . simp [*]
--   | app u v ihu ihv => 
--     sorry -- works 
      
lemma freevars_determine_type {Γ₁ Γ₂ : Context} {t : Term} {σ : Ty} : 
  (∀ x ∈ freeVars t, Γ₁ x = Γ₂ x) → TypeOf Γ₁ t σ → TypeOf Γ₂ t σ := sorry -- we already have this proved the first formalization
  -- intros hfv h₁ 
  -- induction t with 
  -- | var z => 
  --   cases h₁ ; rename_i h₁ 
  --   specialize hfv z (by simp) 
  --   constructor 
  --   rwa [← hfv]
  -- | lam z τ t ih => 
  --   cases h₁ ; rename_i σ' hσ'
  --   constructor 


lemma typeof_rename {Γ : Context} {t : Term} {x y : Var} {σ τ : Ty}:
  fresh t y → (TypeOf (Γ.update x τ) t σ → TypeOf (Γ.update y τ) (rename t x y) σ) := 
by  
  intros hfresh ht
  induction t generalizing Γ σ with 
  | lam z ρ t ih => 
    rcases ht 
    by_cases h : z = x 
    . simp [h]
      constructor 
      rename_i ρ' ht
      rw [h] at ht 
      sorry -- weakening because `y` is fresh in `t`
    . simp [h]
      constructor 
      rename_i ρ' ht 
      specialize @ih (Γ.update z ρ) ρ' sorry /-weakening `ht`-/
      sorry /-permutation-/
  | var z => 
    by_cases h : z = x
    . simp [h]
      constructor
      rcases ht with ⟨ht⟩
      have : τ = σ := by 
        simp [h, Context.update] at ht
        exact ht 
      rw [this]
      simp [Context.update]
    . simp [h]
      simp at hfresh 
      rcases ht with ⟨ht⟩
      constructor 
      simp [h, Context.update] at ht
      push_neg at hfresh; symm at hfresh  
      simp [hfresh, Context.update]
      exact ht
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht 
    simp at hfresh 
    rename_i σ' ht₂ ht₁ 
    specialize @ih₁ Γ _ hfresh.1 ht₁
    specialize @ih₂ Γ _ hfresh.2 ht₂
    simp
    constructor 
    apply ih₁
    apply ih₂

    




      






  

inductive alpha : Term → Term → Prop where 
| rename (t : Term) (σ : Ty) (x y : Var) : 
  fresh t y → alpha (.lam x σ t) (.lam y σ (rename t x y))

example : alpha (.lam "x" .base "x") (.lam "y" .base "y") := by 
  constructor ; simp

example : ¬ alpha (.lam "y" .base (.app "x" "y")) (.lam "x" .base (.app "x" "x")) := by 
  intros halpha ; cases halpha ; simp at *


#check Function.update
lemma typeof_alpha {t u : Term} {Γ : Context} {σ} : alpha t u → TypeOf Γ t σ → TypeOf Γ u σ := by 
  intros halpha 
  induction halpha with 
  | @rename t τ x y hfresh => 
    intros h' 
    cases h' 
    rename_i ρ htp 
    constructor 
    apply @typeof_rename Γ t x y ρ _ hfresh
    assumption


@[simp]
def subst (t : Term) (x : Var) (u : Term) : Term := 
  match t with 
  | .var y => if y = x then u else .var y 
  | .app t₁ t₂ => .app (subst t₁ x u) (subst t₂ x u)
  | t@(.lam y σ t') => if y = x then t else .lam y σ (subst t' x u)

@[simp]
def substitutable (t : Term) (x : Var) (u : Term) : Prop :=
  match t with 
  | .lam y σ t' => 
    y ∉ freeVars u ∧ substitutable t' x u 
  | .app t₁ t₂ => 
    substitutable t₁ x u ∧ substitutable t₂ x u 
  | .var y => 
    x ≠ y

lemma typeof_subst {Γ : Context} {t u : Term} {x : Var} {σ τ : Ty} : 
  substitutable t x u →
  TypeOf (Γ.update x σ) t τ → 
  TypeOf Γ u σ → 
  TypeOf Γ (subst t x u) τ  := 
by 
  intros hsub hΓt hΓu
  induction t generalizing Γ τ with 
  | var y => 
    by_cases h : y = x
    . rw [h] at hΓt ⊢
      have : σ = τ := by 
        rcases hΓt with ⟨hΓt⟩
        simp [Context.update] at hΓt
        exact hΓt
      rw [← this]
      simpa
    . simp [h]
      rcases hΓt with ⟨hΓt⟩
      constructor 
      simp [*, Context.update] at hΓt
      exact hΓt
  | lam y ρ t ih => 
    simp?
    rcases hΓt <;> rename_i ρ' hΓt
    -- constructor 
    by_cases h : y = x 
    . simp [h]
      constructor
      simp at hsub 
      sorry -- because Γ, z : _ ⊢ M : type ∧ z ∉ FV(M)   →    Γ ⊢ M : type
    . simp [h]
      constructor 
      -- rename_i ρ' hΓt
      specialize @ih (Γ.update y ρ) ρ'
      simp [substitutable] at hsub 
      specialize ih hsub.2 sorry sorry  -- weakening and permutation
      assumption
  | app => sorry -- should be routine

      

  

inductive beta : Term → Term → Prop where 
/-- if `t =α t'` and `substitutable t' x u`, then `λ x : σ, t  ->β  t'[x := u]` -/
| redex {t t' u : Term} {x : Var} {σ : Ty} :
  alpha t t' → substitutable t' x u → beta (.app (.lam x σ t) u) (subst t' x u)

lemma typeof_beta {Γ : Context} {t u : Term} {σ : Ty} :
  beta t u → TypeOf Γ t σ → TypeOf Γ u σ := by 
  intros hbeta ht 
  induction hbeta with 
  | @redex t t' s x σ halpha hsubst => 
    rename_i τ 
    cases ht 
    rename_i hs σ' hlam
    cases hlam ; rename_i hlam
    have : TypeOf (Γ.update x σ) t' τ := by 
      apply typeof_alpha halpha
      exact hlam 
    apply typeof_subst hsubst this σ'
    

 


    

    

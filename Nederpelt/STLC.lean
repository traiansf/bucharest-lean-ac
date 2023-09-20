import Mathlib.Data.Finset.Basic

set_option autoImplicit false 

inductive 𝕋 (𝕍 : Type) : Type
| TConst : 𝕍    → 𝕋 𝕍
| To   : 𝕋 𝕍 → 𝕋 𝕍 → 𝕋 𝕍
deriving DecidableEq

inductive Λ (V : Type) (𝕍 : Type) : Type
| Var  : V → Λ V 𝕍
| App  : Λ V 𝕍 → Λ V 𝕍 → Λ V 𝕍 
| Lam  : V → 𝕋 𝕍 → Λ V 𝕍 → Λ V 𝕍

inductive TCtxt (V : Type) (𝕍 : Type) : Type
| Empty       : TCtxt V 𝕍
| VarCtxt     : V → 𝕋 𝕍 → TCtxt V 𝕍 → TCtxt V 𝕍  

variable {V 𝕍 : Type}
variable [DecidableEq V] [DecidableEq 𝕍] 

notation:9 σ " →' " τ => 𝕋.To σ τ 
notation:9 Γ ";; " x " : " σ => TCtxt.VarCtxt x σ Γ
notation:9 "λ' " x " : " σ ", " M => Λ.Lam x σ M

instance : Coe V (Λ V 𝕍) where
  coe := .Var 
instance : Coe 𝕍 (𝕋 𝕍) where
  coe := .TConst
instance : CoeFun (Λ V 𝕍) (fun _ => Λ V 𝕍 → Λ V 𝕍) where
  coe := .App 

@[simp]
def freeTConstsOfType : 𝕋 𝕍 → Finset 𝕍
| .TConst α => {α}
| .To σ₀ σ₁ => (freeTConstsOfType σ₀) ∪ (freeTConstsOfType σ₁)

@[simp]
def freeVarsOfTerm : Λ V 𝕍 → Finset V
| .Var x     => {x}
| .App M N   => (freeVarsOfTerm M) ∪ (freeVarsOfTerm N)
| .Lam x _ M => (freeVarsOfTerm M).erase x

@[simp]
def subVarInTerm (x : V) (N : Λ V 𝕍) : Λ V 𝕍 → Λ V 𝕍
| .Var x'     => if x = x'
                 then N 
                 else Λ.Var x'
| .App M M'   => Λ.App (subVarInTerm x N M) (subVarInTerm x N M')
-- | .TApp M τ   => Λ.TApp (subVarInTerm x N M) τ
| .Lam x' τ M => Λ.Lam x' τ (if x = x' then M else subVarInTerm x N M)
-- | .TLam α M   => Λ.TLam α (subVarInTerm x N M)


@[simp]
def AlphaEquiv' (var_map : V → Option V) : Λ V 𝕍 → Λ V 𝕍 → Prop
| .Var x₀, .Var x₁ => var_map x₀ = some x₁ ∨ (var_map x₀ = none ∧ x₀ = x₁) 
| .App M₀ M₀', .App M₁ M₁' => 
  AlphaEquiv' var_map M₀ M₁ ∧
  AlphaEquiv' var_map M₀' M₁'
| .Lam x₀ σ₀ M₀, .Lam x₁ σ₁ M₁ =>
  AlphaEquiv' (λ vn => if vn = x₀ then some x₁ else var_map vn) M₀ M₁ ∧
  σ₀ = σ₁
| _, _ => False
  
@[simp]
def AlphaEquiv (M N : Λ V 𝕍) : Prop := AlphaEquiv' (λ _ => .none) M N


@[simp]
def DomTCtxt : TCtxt V 𝕍 → Finset V
| .Empty           => {}
| .VarCtxt x _ Γ   => (DomTCtxt Γ) ∪ {x}

@[simp]
def getType (x : V) : TCtxt V 𝕍 → Option (𝕋 𝕍)
| .Empty => none
| .VarCtxt x' σ Γ => 
    if x = x'
    then some σ
    else getType x Γ

lemma getTypeRebind {Γ : TCtxt V 𝕍} {y : V} {σ σ' : 𝕋 𝕍} :
    ∀ x : V, getType x ((Γ;; y : σ);; y : σ') = getType x (Γ;; y : σ') := by
  introv; simp; split_ifs <;> rfl

lemma getTypeReorder {Γ : TCtxt V 𝕍} {x y : V} {σ σ' : 𝕋 𝕍} :
    x ≠ y → 
      ∀ {z : V}, getType z ((Γ;;x : σ);; y : σ') = getType z ((Γ;;y : σ');; x : σ) := by
  intro h z
  by_cases h' : z = x
  · simp [h, h']
  · by_cases h'' : z = y
    · simp [h', h'']
      split_ifs with h
      · exfalso; rw [h''] at h'; exact h' h 
      · rfl;
    · simp [h', h'']

lemma typeOfDefinedOfInTCtxt : 
  ∀ (Γ : TCtxt V 𝕍) (x : V), 
    x ∈ DomTCtxt Γ → (∃ σ : 𝕋 𝕍, (getType x Γ) = (some σ)) := by
  intros Γ x
  induction' Γ
  · simp
  case VarCtxt x' σ Γ h_ind =>
  simp only [DomTCtxt, Finset.mem_union, Finset.mem_singleton, getType]
  by_cases h' : x = x' 
  . simp [h']  
  · simp only [h', or_false, ite_false]; assumption

@[simp]
def typeOf (Γ : TCtxt V 𝕍) : Λ V 𝕍 → Option (𝕋 𝕍)
| .Var x => getType x Γ
| .App M N => 
  match typeOf Γ M with
  | .some (τ →' σ) => 
    if typeOf Γ N = some τ
    then some σ
    else none
  | _               => none
| .Lam x σ M => 
  match typeOf (.VarCtxt x σ Γ) M with 
  | .some τ => some (.To σ τ)
  | _       => none


lemma ctxtTypeOfPreservation {M : Λ V 𝕍} : 
  ∀ {Γ Γ': TCtxt V 𝕍},
    (∀ x : V, x ∈ freeVarsOfTerm M → getType x Γ = getType x Γ') →
        typeOf Γ M = typeOf Γ' M := by
  induction M with
  | Var x => intro Γ Γ' h; apply h; simp
  | App M N ih₁ ih₂ =>
    intro Γ Γ' h
    have h₁ (x : V) (h' : x ∈ freeVarsOfTerm M) : getType x Γ = getType x Γ' := by
      exact h x (by simp only [freeVarsOfTerm, Finset.mem_union, h', true_or])
    have h₂ (x : V) (h' : x ∈ freeVarsOfTerm N) : getType x Γ = getType x Γ' := by
      exact h x (by simp only [freeVarsOfTerm, Finset.mem_union, h', or_true])
    simp [ih₁ h₁, ih₂ h₂]
  | Lam y σ M ih => 
    intro Γ Γ' h
    have h (x : V) (h' : x ∈ freeVarsOfTerm M) : getType x (Γ;; y : σ) = getType x (Γ';; y : σ) := by
      by_cases h'' : x = y <;> simp[h'']
      exact h x (Finset.mem_erase_of_ne_of_mem h'' h')
    simp [ih h]

@[simp]
def typingJudgement
    (Γ : TCtxt V 𝕍) (M : Λ V 𝕍) (σ : 𝕋 𝕍) : Prop :=
  typeOf Γ M = some σ

notation:10 Γ " ⊢ " M " : " σ => typingJudgement Γ M σ
notation:9  M " =ₐ " N => AlphaEquiv M N 

example {α : 𝕍} {x : V} : .Empty ⊢ (λ' x : (.TConst α), (.Var x)) : (α →' α) := by
  simp

@[simp]
lemma unfoldTypingJudgement {Γ : TCtxt V 𝕍} {M : Λ V 𝕍} {σ : 𝕋 𝕍} :
  (Γ ⊢ M : σ) → (typeOf Γ M = some σ) := id

lemma var_rule (Γ : TCtxt V 𝕍) (x : V) (σ : 𝕋 𝕍) :
  getType x Γ = some σ ↔ (Γ ⊢ x : σ) := by simp

lemma appl_rule {Γ : TCtxt V 𝕍} {M N : Λ V 𝕍} {τ : 𝕋 𝕍} : 
  (∃ σ, (Γ ⊢ M : σ →' τ) ∧ (Γ ⊢ N : σ)) ↔ (Γ ⊢ M N : τ) := by
    apply Iff.intro
    · rintro ⟨σ, h, h'⟩; unfold typingJudgement at *; simp [h, h']
    · intro h
      simp only [typingJudgement, typeOf] at h 
      generalize h' : typeOf Γ M = x; rw [h'] at h
      match x with
        | none => simp at h
        | some val => 
          match val with
          | .To σ τ' => 
            use σ
            simp only at h 
            split_ifs at h with h''
            simp only [Option.some.injEq] at h 
            rw [h] at h'
            exact ⟨h', h''⟩

lemma abst_rule (Γ : TCtxt V 𝕍) (M : Λ V 𝕍) (x : V) (σ τ : 𝕋 𝕍) :
  ((Γ;; x : σ) ⊢ M : τ) ↔ (Γ ⊢ (λ' x : σ, M) : σ →' τ) := by
  apply Iff.intro
  · intros h; unfold typingJudgement at *; simp [h]
  · intros h; simp at *
    generalize h' : typeOf (Γ;; x : σ) M = aux; rw [h'] at h
    match aux with
    | .some τ' => simp at h; simp [h]

lemma typeUniqueness (Γ : TCtxt V 𝕍) (M : Λ V 𝕍) (σ τ : 𝕋 𝕍) :
  (Γ ⊢ M : σ) → (Γ ⊢ M : τ) → σ = τ := by
    intros h h'; unfold typingJudgement at *; rw [h, Option.some.injEq] at h'; assumption
  
lemma AlphaEquivPreservesType' :
  ∀ {M' M : Λ V 𝕍} {Γ Γ' : TCtxt V 𝕍} {σ : 𝕋 𝕍}
    {var_map : V → Option V},
      AlphaEquiv' var_map M M' →
      (∀ x : V, 
        (var_map x = none ∧ getType x Γ = getType x Γ') ∨
        (∃ y : V, var_map x = some y ∧ getType x Γ = getType y Γ')
      )
      → (Γ ⊢ M : σ) → (Γ' ⊢ M' : σ) := by
  intros M'
  induction M' with
  | Var y =>
    introv
    intros alpha_equiv ctxt_equiv
    match M with
    | .Var x =>
      simp at alpha_equiv
      rcases alpha_equiv with var_map_x_to_y | ⟨var_map_x_is_none, x_eq_y⟩
      · specialize ctxt_equiv x 
        simp [var_map_x_to_y] at ctxt_equiv
        simp [ctxt_equiv]
      · simp
        specialize ctxt_equiv x
        rw [←x_eq_y]
        simp [var_map_x_is_none] at ctxt_equiv
        simp [ctxt_equiv]
  | App M₀' M₁' ih₀ ih₁ =>
    introv 
    intros alpha_equiv ctxt_equiv h
    match M with
    | .App M₀ M₁ =>
      simp at alpha_equiv
      rw [←appl_rule] at h
      rcases h with ⟨τ, h₀, h₁⟩
      specialize ih₀ alpha_equiv.1 ctxt_equiv h₀
      specialize ih₁ alpha_equiv.2 ctxt_equiv h₁
      simp at ih₀ ih₁
      simp [ih₀, ih₁]
  | Lam x' τ' M' ih =>
    introv
    intros alpha_equiv ctxt_equiv h
    match M with
    | .Lam x τ M =>
      simp at alpha_equiv
      simp at h
      generalize h' : typeOf (Γ;; x : τ) M = aux
      rw [h'] at h
      match aux with
      | some σ' =>
        simp at h
        rw [alpha_equiv.2] at h
        rw [←h]
        simp
        have ctxt_equiv' : 
         ∀ (y : V), 
             ((if y = x then some x' else var_map y) = none ∧ getType y (Γ;; x : τ) = getType y (Γ';; x' : τ')) ∨ 
             (∃ z, (if y = x then some x' else var_map y) = some z ∧ getType y (Γ;; x : τ) = getType z (Γ';; x' : τ')) := by 
          introv
          by_cases h : y = x
          simp [h, alpha_equiv.2]
        specialize ih alpha_equiv.1 ctxt_equiv' h'
        rw [ih]

lemma AlphaEquivPreservesType :
  ∀ {M M' : Λ V 𝕍} {Γ : TCtxt V 𝕍} {σ : 𝕋 𝕍},
      (M =ₐ M') → (Γ ⊢ M : σ) → (Γ ⊢ M' : σ) := by
  introv; intro h h'
  exact AlphaEquivPreservesType' h (by introv; simp) h'
  

def lambda2BetaReduction : Λ V 𝕍 → Λ V 𝕍 → Prop
| .Lam x σ M, R => ∃ M', R = Λ.Lam x σ M' ∧ lambda2BetaReduction M M'
| .App M N, R => 
    (∃ M' N' : Λ V 𝕍, R = M' N' ∧
      (
        (lambda2BetaReduction M M' ∧ N' = N) ∨
        (lambda2BetaReduction N N' ∧ M' = M)
      )
    ) ∨
    (
      match M with
      | .Lam x σ M' => R = subVarInTerm x N M'
      | _           => False
    ) 
| .Var _, _ => False

notation:10 M " ↠ " M' => lambda2BetaReduction M M'

lemma varSubPreservesTypeVar 
  {Γ : TCtxt V 𝕍} {N : Λ V 𝕍} {x y : V} {σ : 𝕋 𝕍} : (Γ ⊢ N : σ) →
    typeOf (Γ;; x : σ) (Λ.Var y) = typeOf Γ (subVarInTerm x N (Λ.Var y)) := by
  intro h
  simp
  split_ifs with h' h'' h''
  · rw [h]
  · exfalso; exact h'' (Eq.symm h')
  · exfalso; exact h' (Eq.symm h'')
  · simp

lemma varSubPreservesType {M N : Λ V 𝕍} {x : V} {σ : 𝕋 𝕍} :
    ∀ {Γ : TCtxt V 𝕍}, (Γ ⊢ N : σ) → typeOf (Γ;; x : σ) M = typeOf Γ (subVarInTerm x N M) := by sorry 

      
theorem betaReductionPreservesType {Γ : TCtxt V 𝕍} {M M' : Λ V 𝕍} {σ : 𝕋 𝕍} :
  (M ↠ M') → (Γ ⊢ M : σ) → (Γ ⊢ M' : σ) := by
    sorry

      

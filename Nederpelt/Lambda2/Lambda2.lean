import Mathlib.Data.Finset.Basic

inductive 𝕋2 (𝕍 : Type) : Type
| TVar : 𝕍    → 𝕋2 𝕍
| To   : 𝕋2 𝕍 → 𝕋2 𝕍 → 𝕋2 𝕍
| TTo  : 𝕍 → 𝕋2 𝕍 → 𝕋2 𝕍
deriving DecidableEq

inductive Λ2 (V : Type) (𝕍 : Type) : Type
| Var  : V → Λ2 V 𝕍
| App  : Λ2 V 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍 
| TApp : Λ2 V 𝕍 → 𝕋2 𝕍 → Λ2 V 𝕍
| Lam  : V → 𝕋2 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍
| TLam : 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍

inductive TCtxt2 (V : Type) (𝕍 : Type) : Type
| Empty       : TCtxt2 V 𝕍
| TypeVarCtxt : 𝕍 → TCtxt2 V 𝕍 → TCtxt2 V 𝕍
| VarCtxt     : V → 𝕋2 𝕍 → TCtxt2 V 𝕍 → TCtxt2 V 𝕍  

notation:9 σ " →' " τ => 𝕋2.To σ τ 
notation:9 Γ ";; " x " : " σ => TCtxt2.VarCtxt x σ Γ
notation:9 Γ ";; " α " : * " => TCtxt2.TypeVarCtxt α Γ
notation:9 "Π " α " : *, " σ => 𝕋2.TTo α σ
notation:9 "λ' " x " : " σ ", " M => Λ2.Lam x σ M
notation:9 "λ' " α " : *, " M => Λ2.TLam α M
notation:9 M " ⟪" σ "⟫" => Λ2.TApp M σ

variable {V 𝕍 : Type}
variable [DecidableEq V] [DecidableEq 𝕍] 

@[simp]
def freeTVarsOfType : 𝕋2 𝕍 → Finset 𝕍
| .TVar α => {α}
| .To σ₀ σ₁ => (freeTVarsOfType σ₀) ∪ (freeTVarsOfType σ₁)
| .TTo α σ => (freeTVarsOfType σ).erase α

@[simp]
def boundTVarsOfType : 𝕋2 𝕍 → Finset 𝕍
| .TVar _   => {} 
| .To σ₀ σ₁ => (boundTVarsOfType σ₀) ∪ (boundTVarsOfType σ₁)
| .TTo α σ  => (boundTVarsOfType σ) ∪ {α}

@[simp]
def freeVarsOfTerm : Λ2 V 𝕍 → Finset V
| .Var x     => {x}
| .App M N   => (freeVarsOfTerm M) ∪ (freeVarsOfTerm N)
| .TApp M _  => freeVarsOfTerm M
| .Lam x _ M => (freeVarsOfTerm M).erase x
| .TLam _ M  => freeVarsOfTerm M

@[simp]
def freeTVarsOfTerm : Λ2 V 𝕍 → Finset 𝕍
| .Var  _     => {}
| .App  M N   => (freeTVarsOfTerm M) ∪ (freeTVarsOfTerm N)
| .TApp M σ   => (freeTVarsOfTerm M) ∪ (freeTVarsOfType σ)
| .Lam  _ σ M => (freeTVarsOfTerm M) ∪ (freeTVarsOfType σ)
| .TLam α M   => (freeTVarsOfTerm M).erase α

@[simp]
def subTVarInType (α : 𝕍) (σ : 𝕋2 𝕍) : 𝕋2 𝕍 → 𝕋2 𝕍
| .TVar α' => 
  if α = α'
  then σ
  else .TVar α'
| .To τ τ' => .To (subTVarInType α σ τ) (subTVarInType α σ τ')
| .TTo α' τ => 
  .TTo α' (if α = α' then τ else (subTVarInType α σ τ))

@[simp]
def subFreeTVarsInType (tvar_map : 𝕍 → Option 𝕍) : 𝕋2 𝕍 → 𝕋2 𝕍
| .TVar α => 
  .TVar (match tvar_map α with
          | .some β => β
          | .none   => α)
| .To τ τ' => .To (subFreeTVarsInType tvar_map τ) (subFreeTVarsInType tvar_map τ')
| .TTo α τ => 
  .TTo α (subFreeTVarsInType (λtv => if tv = α then .none else tvar_map tv) τ)

@[simp]
def subVarInTerm (x : V) (N : Λ2 V 𝕍) : Λ2 V 𝕍 → Λ2 V 𝕍
| .Var x'     => if x = x'
                 then N 
                 else Λ2.Var x'
| .App M M'   => Λ2.App (subVarInTerm x N M) (subVarInTerm x N M')
| .TApp M τ   => Λ2.TApp (subVarInTerm x N M) τ
| .Lam x' τ M => Λ2.Lam x' τ (if x = x' then M else subVarInTerm x N M)
| .TLam α M   => Λ2.TLam α (subVarInTerm x N M)

@[simp]
def subTVarInTerm (α : 𝕍) (σ : 𝕋2 𝕍) : Λ2 V 𝕍 → Λ2 V 𝕍
| .Var x'     => Λ2.Var x'
| .App M M'   => Λ2.App (subTVarInTerm α σ M) (subTVarInTerm α σ M')
| .TApp M τ   => Λ2.TApp (subTVarInTerm α σ M) (subTVarInType α σ τ)
| .Lam x' τ M => Λ2.Lam x' (subTVarInType α σ τ) (subTVarInTerm α σ M)
| .TLam α' M   => if α = α'
                  then Λ2.TLam α' M
                  else Λ2.TLam α' (subTVarInTerm α σ M) 

@[simp]
def TAlphaEquiv' (tvar_map : 𝕍 → Option 𝕍) : 𝕋2 𝕍 → 𝕋2 𝕍 → Prop
| .TVar α₀, .TVar α₁ => 
  (tvar_map α₀ = some α₁) ∨ (tvar_map α₀ = none ∧ α₀ = α₁)
| .To σ₀ τ₀, .To σ₁ τ₁ => 
  TAlphaEquiv' tvar_map σ₀ σ₁ ∧ TAlphaEquiv' tvar_map τ₀ τ₁
| .TTo α₀ σ₀, .TTo α₁ σ₁ => 
  TAlphaEquiv' (λ tn => if tn = α₀ then some α₁ else tvar_map tn) σ₀ σ₁
| _, _ => False


@[simp]
def AlphaEquiv' (var_map : V → Option V) (tvar_map : 𝕍 → Option 𝕍) : Λ2 V 𝕍 → Λ2 V 𝕍 → Prop
| .Var x₀, .Var x₁ => var_map x₀ = some x₁ ∨ (var_map x₀ = none ∧ x₀ = x₁) 
| .App M₀ M₀', .App M₁ M₁' => 
  AlphaEquiv' var_map tvar_map M₀ M₁ ∧
  AlphaEquiv' var_map tvar_map M₀' M₁'
| .TApp M₀ σ₀, .TApp M₁ σ₁ => 
  AlphaEquiv' var_map tvar_map M₀ M₁ ∧ TAlphaEquiv' tvar_map σ₀ σ₁
| .Lam x₀ σ₀ M₀, .Lam x₁ σ₁ M₁ =>
  AlphaEquiv' (λ vn => if vn = x₀ then some x₁ else var_map vn) tvar_map M₀ M₁ ∧
  TAlphaEquiv' tvar_map σ₀ σ₁
| .TLam α₀ M₀, .TLam α₁ M₁ => 
  AlphaEquiv' var_map (λ tn => if tn = α₀ then some α₁ else tvar_map tn) M₀ M₁
| _, _ => False
  
@[simp]
def AlphaEquiv (M N : Λ2 V 𝕍) : Prop := AlphaEquiv' (λ _ => .none) (λ _ => .none) M N

lemma AlphaEquivSub' {tvar_map tvar_map' : 𝕍 → Option 𝕍} {σ : 𝕋2 𝕍} :
  (∀ α, tvar_map α = tvar_map' α ∨ (tvar_map α = some α ∧ tvar_map' α = none)) →
    TAlphaEquiv' tvar_map σ (subFreeTVarsInType tvar_map' σ) := by
  revert tvar_map tvar_map'
  induction σ with
  | TVar α => 
    introv; intro h
    specialize h α
    rcases h with h | h
    · simp; revert h; cases tvar_map α <;> (intro h; simp [←h])
    · simp; rw [h.1, h.2]; simp
  | To σ₀ σ₁ ih₀ ih₁ =>
    introv; intro h; simp [ih₀ h, ih₁ h]
  | TTo α σ ih =>
    introv; intro h
    simp; apply ih
    intros β
    split_ifs with h'
    · simp[h']
    · simp; exact h _ 

lemma AlphaEquivSub {tvar_map : 𝕍 → Option 𝕍} {σ : 𝕋2 𝕍} : TAlphaEquiv' tvar_map σ (subFreeTVarsInType tvar_map σ) := AlphaEquivSub' (by simp)

@[simp]
def TDomTCtxt : TCtxt2 V 𝕍 → Finset 𝕍
| .Empty           => {} 
| .TypeVarCtxt α Γ => {α} ∪ (TDomTCtxt Γ)
| .VarCtxt _ _ Γ   => TDomTCtxt Γ

@[simp]
def DomTCtxt : TCtxt2 V 𝕍 → Finset V
| .Empty           => {} 
| .TypeVarCtxt _ Γ => DomTCtxt Γ
| .VarCtxt x _ Γ   => (DomTCtxt Γ) ∪ {x}

@[simp]
def getType (x : V) : TCtxt2 V 𝕍 → Option (𝕋2 𝕍)
| .Empty => none
| .TypeVarCtxt _ Γ => getType x Γ 
| .VarCtxt x' σ Γ => 
    if x = x'
    then some σ
    else getType x Γ

lemma getTypeRebind {Γ : TCtxt2 V 𝕍} {y : V} {σ σ' : 𝕋2 𝕍} :
    ∀ x : V, getType x ((Γ;; y : σ);; y : σ') = getType x (Γ;; y : σ') := by
  introv; simp; split_ifs <;> rfl

lemma getTypeReorder {Γ : TCtxt2 V 𝕍} {x y : V} {σ σ' : 𝕋2 𝕍} :
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
  ∀ (Γ : TCtxt2 V 𝕍) (x : V), 
    x ∈ DomTCtxt Γ → (∃ σ : 𝕋2 𝕍, (getType x Γ) = (some σ)) := by
  intros Γ x
  induction' Γ with α Γ h_ind x' σ Γ h_ind
  · simp
  · simp only [DomTCtxt, getType]; assumption
  · simp only [DomTCtxt, Finset.mem_union, Finset.mem_singleton, getType];  
    by_cases h' : x = x'
    · simp [h']
    · simp only [h', or_false, ite_false]; assumption

def wellFormedTCtxt : TCtxt2 V 𝕍 → Prop 
| .Empty => True
| .TypeVarCtxt α Γ => α ∉ TDomTCtxt Γ ∧ wellFormedTCtxt Γ
| .VarCtxt x σ Γ => x ∉ DomTCtxt Γ ∧ 
                    ∀ α : 𝕍, 
                      α ∈ freeTVarsOfType σ → 
                        α ∈ TDomTCtxt Γ ∧ 
                    wellFormedTCtxt Γ

def formationRule (Γ : TCtxt2 V 𝕍) (σ : 𝕋2 𝕍) : Prop := 
  freeTVarsOfType σ ⊆ TDomTCtxt Γ

instance {Γ : TCtxt2 V 𝕍} {σ : 𝕋2 𝕍} : Decidable (formationRule Γ σ) := 
  Finset.decidableSubsetFinset 

@[simp]
def typeOf (Γ : TCtxt2 V 𝕍) : Λ2 V 𝕍 → Option (𝕋2 𝕍)
| .Var x => getType x Γ
| .App M N => 
  match typeOf Γ M with
  | .some (.To τ σ) => 
    if typeOf Γ N = some τ
    then some σ
    else none
  | _               => none
| .TApp M σ => 
  match typeOf Γ M with
  | .some (.TTo α τ) => 
    if formationRule Γ σ
    then some (subTVarInType α σ τ)
    else none
  | _                => none
| .Lam x σ M => 
  match typeOf (.VarCtxt x σ Γ) M with 
  | .some τ => some (.To σ τ)
  | _       => none
| .TLam α M => 
  if α ∉ TDomTCtxt Γ ∧ ∀ (x : V) (σ : 𝕋2 𝕍), getType x Γ = some σ ∧ α ∉ boundTVarsOfType σ 
  then 
    match typeOf (.TypeVarCtxt α Γ) M with
    | .some τ => some (.TTo α τ)
    | _       => none
  else none

-- x : Π α : *, ... 

-- lemma ctxtTypeOfPreservation {M : Λ2 V 𝕍} : 
--   ∀ {Γ Γ': TCtxt2 V 𝕍},
--     (∀ x : V, x ∈ freeVarsOfTerm M → getType x Γ = getType x Γ') → 
--       TDomTCtxt Γ = TDomTCtxt Γ' → 
--         typeOf Γ M = typeOf Γ' M := by
--   induction M with
--   | Var x => intro Γ Γ' h _; apply h; simp
--   | App M N ih₁ ih₂ =>
--     intro Γ Γ' h h'
--     have h₁ (x : V) (h' : x ∈ freeVarsOfTerm M) : getType x Γ = getType x Γ' := by
--       exact h x (by simp only [freeVarsOfTerm, Finset.mem_union, h', true_or])
--     have h₂ (x : V) (h' : x ∈ freeVarsOfTerm N) : getType x Γ = getType x Γ' := by
--       exact h x (by simp only [freeVarsOfTerm, Finset.mem_union, h', or_true])
--     simp [ih₁ h₁ h', ih₂ h₂ h']
--   | TApp M σ ih => 
--     intro Γ Γ' h h'
--     simp [ih h, formationRule, h']
--   | Lam y σ M ih => 
--     intro Γ Γ' h h'
--     have h (x : V) (h' : x ∈ freeVarsOfTerm M) : getType x (Γ;; y : σ) = getType x (Γ';; y : σ) := by
--       by_cases h'' : x = y <;> simp[h'']
--       exact h x (Finset.mem_erase_of_ne_of_mem h'' h')
--     simp [ih h h']
--   | TLam α M ih =>
--     intro Γ Γ' h h'
--     have h (x : V) (h' : x ∈ freeVarsOfTerm M) : 
--       getType x (Γ;; α : * ) = getType x (Γ';; α : * ) := by simp [h x h']
--     specialize ih h
--     unfold TDomTCtxt at ih
--     rw [h'] at ih
--     specialize ih (by rfl)
--     simp [ih]

@[simp]
def typingJudgement
    (Γ : TCtxt2 V 𝕍) (M : Λ2 V 𝕍) (σ : 𝕋2 𝕍) : Prop :=
  typeOf Γ M = some σ

notation:10 Γ " ⊢ " M " : " σ => typingJudgement Γ M σ
notation:10 Γ " ⊢ " σ " : * " => formationRule Γ σ
notation:9  M " =ₐ " N => AlphaEquiv M N 

example {Γ : TCtxt2 V 𝕍} {σ : 𝕋2 𝕍} : 
  ∀ {M : Λ2 V 𝕍}, (Γ ⊢ M : σ) → ∀ α : 𝕍, α ∈ boundTVarsOfType σ → α ∉ TDomTCtxt Γ := by
  intros M 
  induction M with
  | Var x =>
    intros h α
    

@[simp]
lemma unfoldTypingJudgement {Γ : TCtxt2 V 𝕍} {M : Λ2 V 𝕍} {σ : 𝕋2 𝕍} :
  (Γ ⊢ M : σ) → (typeOf Γ M = some σ) := id

instance : Coe V (Λ2 V 𝕍) where
  coe := .Var 
instance : CoeFun (Λ2 V 𝕍) (fun _ => Λ2 V 𝕍 → Λ2 V 𝕍) where
  coe := .App 

lemma var_rule (Γ : TCtxt2 V 𝕍) (x : V) (σ : 𝕋2 𝕍) :
  getType x Γ = some σ ↔ (Γ ⊢ x : σ) := by simp

lemma appl_rule {Γ : TCtxt2 V 𝕍} {M N : Λ2 V 𝕍} {τ : 𝕋2 𝕍} : 
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

-- lemma abst_rule (Γ : TCtxt2 V 𝕍) (M : Λ2 V 𝕍) (x : V) (σ τ : 𝕋2 𝕍) :
--   ((Γ;; x : σ) ⊢ M : τ) → (Γ ⊢ (λ' x : σ, M) : σ →' τ) := by
--     intros h; unfold typingJudgement at *; simp [h]

lemma appl₂_rule (Γ : TCtxt2 V 𝕍) (α : 𝕍) (M : Λ2 V 𝕍) (σ τ : 𝕋2 𝕍) :
  ((Γ ⊢ M : Π α : *, σ) ∧ (Γ ⊢ τ : *)) → (Γ ⊢ M ⟪τ⟫ : subTVarInType α τ σ) := by
    intros h; simp only [typingJudgement, typeOf] at h; simp [h]




      








-- lemma abst₂_rule (Γ : TCtxt2 V 𝕍) (α : 𝕍) (M : Λ2 V 𝕍) (σ : 𝕋2 𝕍) :
--   ((Γ;; α : *) ⊢ M : σ) → (Γ ⊢ (λ' α : *, M) : (Π α : *, σ)) := by
--     intros h; unfold typingJudgement at h; simp [h]

lemma typeUniqueness (Γ : TCtxt2 V 𝕍) (M : Λ2 V 𝕍) (σ τ : 𝕋2 𝕍) :
  (Γ ⊢ M : σ) → (Γ ⊢ M : τ) → σ = τ := by
    intros h h'; unfold typingJudgement at *; rw [h, Option.some.injEq] at h'; assumption
  
#check subFreeTVarsInType

lemma AlphaEquivPreservesType' :
  ∀{M' M : Λ2 V 𝕍} {Γ Γ' : TCtxt2 V 𝕍} {σ σ' : 𝕋2 𝕍}
    {var_map : V → Option V} {tvar_map : 𝕍 → Option 𝕍},
      AlphaEquiv' var_map tvar_map M M' → 
      (∀x : V, 
        (∃ y τ τ', var_map x = .some y ∧ 
          getType x Γ = .some τ ∧
          getType y Γ' = .some τ' ∧
          τ' = subFreeTVarsInType tvar_map τ) ∨
        (var_map x = .none ∧ 
          ((getType x Γ = .none ∧ getType x Γ' = .none) ∨
          (∃ τ τ', 
            getType x Γ  = .some τ ∧
            getType x Γ' = .some τ' ∧
            τ' = subFreeTVarsInType tvar_map τ 
          ))
        )
      ) → 
      (∀ α, 
        α ∈ TDomTCtxt Γ →
          (tvar_map α = none ∧ α ∈ TDomTCtxt Γ') ∨ 
          (∃ β, tvar_map α = some β ∧ β ∈ TDomTCtxt Γ')  
      ) 
      → (Γ ⊢ M : σ) → (Γ' ⊢ M' : σ') → TAlphaEquiv' tvar_map σ σ' := by
  intros M'
  induction M' with
  | Var x => 
    introv 
    intros alpha_equiv ctxt_var_sub ctxt_type_sub h h'
    match M with
    | .Var y =>
      simp at alpha_equiv
      rcases alpha_equiv with alpha_equiv | alpha_equiv
      · specialize ctxt_var_sub y
        simp [alpha_equiv] at ctxt_var_sub 
        simp at h
        simp at h'
        rw [h, h'] at ctxt_var_sub
        simp at ctxt_var_sub
        rw [ctxt_var_sub]
        exact AlphaEquivSub
      · specialize ctxt_var_sub y
        rw [←alpha_equiv.2] at h'
        simp at h h'
        simp [alpha_equiv.1, h, h'] at ctxt_var_sub 
        rw [ctxt_var_sub]
        exact AlphaEquivSub
  | App M₀' M₁' ih₀ ih₁ =>
    introv 
    intros alpha_equiv ctxt_var_sub ctxt_type_sub h h'
    match M with
    | .App M₀ M₁ =>
      simp at alpha_equiv
      rw [←appl_rule] at h h'
      specialize ih₀ alpha_equiv.1 ctxt_var_sub ctxt_type_sub h.2.1 h'.2.1 
      simp at ih₀
      exact ih₀.2
  | TApp M' τ' ih =>
    introv 
    intros alpha_equiv ctxt_var_sub ctxt_type_sub M_type_σ M'_type_σ'
    match M with
    | .TApp M τ =>
      simp at alpha_equiv M_type_σ M'_type_σ'
      generalize h  : typeOf Γ M   = aux;  rw [h]  at M_type_σ
      generalize h' : typeOf Γ' M' = aux'; rw [h'] at M'_type_σ'
      match aux with
      | .some (Π α : *, γ) =>
        match aux' with
        | .some (Π α' : *, γ') =>
          specialize ih alpha_equiv.1 ctxt_var_sub ctxt_type_sub h h'
          simp at ih
          simp at M_type_σ M'_type_σ'
          split_ifs at M_type_σ with τ_wf <;> split_ifs at M'_type_σ' with τ'_wf
          · simp at M_type_σ M'_type_σ'
            rw [←M_type_σ, ←M'_type_σ']







        





  -- intros N
  -- induction N with
  -- | Var x =>
  --   introv; intros alpha_equiv ctxt_var_sub _ h
  --   match M with
  --   | .Var y =>
  --     simp at alpha_equiv
  --     rcases alpha_equiv with alpha_equiv | alpha_equiv
  --     · simp at h
  --       specialize ctxt_var_sub y 
  --       simp [alpha_equiv, h] at ctxt_var_sub
  --       use (subFreeTVarsInType tvar_map σ)
  --       exact ⟨ctxt_var_sub, AlphaEquivSub⟩
  --     · simp at h
  --       specialize ctxt_var_sub y 
  --       simp [alpha_equiv.1, h] at ctxt_var_sub
  --       rw [←alpha_equiv.2]
  --       use (subFreeTVarsInType tvar_map σ)
  --       exact ⟨ctxt_var_sub, AlphaEquivSub⟩ 
  -- | App N₀ N₁ ih₀  ih₁ =>
  --   introv; intros alpha_equiv ctxt_var_sub ctxt_type_sub h
  --   match M with
  --   | .App M₀ M₁ => 
  --     simp at alpha_equiv
  --     rw [←appl_rule] at h 
  --     rcases h with ⟨τ, h, h'⟩
  --     rcases ih₀ alpha_equiv.1 ctxt_var_sub ctxt_type_sub h  with ⟨σ₀, ih₀, α_equiv_0⟩
  --     rcases ih₁ alpha_equiv.2 ctxt_var_sub ctxt_type_sub h' with ⟨σ₁, ih₁, α_equiv_1⟩
  --     match σ₀ with
  --     | .TVar _ => simp at α_equiv_0
  --     | .To τ₀ τ₁ =>
  --       use τ₁
  --       simp at α_equiv_0
  --       apply And.intro _ α_equiv_0.2
  --       rw [←appl_rule]
  --       use σ₁
  --       apply And.intro _ ih₁

  --       --  simp
  --       --  rw [ih₁]
         

  --       --  simp
  --       --  rw [ih₀]
  --       --  simp
  --       --  intro h''; apply h''; 
  --       sorry 
  --     -- unfold subFreeTVarsInType at ih₀
  --     -- simp
  --     -- rw [ih₀, ih₁]
  --     -- simp
  --     | .TTo _ σ => simp at α_equiv_0

  -- | TApp N τ' ih =>
  --   introv; intros alpha_equiv ctxt_var_sub ctxt_type_sub h
  --   match M with
  --   | .TApp M τ =>
  --     simp at alpha_equiv
  --     simp at h
  --     generalize h' : typeOf Γ M = aux
  --     rw [h'] at h
  --     match aux with
  --     | some (Π α'' : *, τ'') => 
  --       specialize ih alpha_equiv.1 ctxt_var_sub ctxt_type_sub h'
  --       split_ifs at h with τ_wf
  --       · simp at h
  --         rw [←h]
  --         unfold subFreeTVarsInType at ih
  --         simp
  --         rw [ih]
  --         simp
  --         have τ'_wf : Γ' ⊢ τ' : * := sorry 
  --         simp [τ'_wf]
  --         rcases alpha_equiv with ⟨alpha_equiv, τ_eq_τ'⟩
          -- unfold TAlphaEquiv' at τ_eq_τ'

          



        -- unfold subFreeTVarsInType at ih
        -- split_ifs at h with h''
        -- simp at h
        -- rw [←h]
        -- simp
        -- rw [ih]
        -- simp
        -- have τ'_wf : Γ' ⊢ τ' : * := sorry 
        -- simp [τ'_wf]
        -- have bla : 
        --   ∀ {α : 𝕍} {σ τ : 𝕋2 𝕍} {tvar_map : 𝕍 → Option 𝕍},  
        --     tvar_map α = none → 
        --     subTVarInType α σ (subFreeTVarsInType tvar_map τ) = subFreeTVarsInType tvar_map (subTVarInType α σ τ) := by sorry
        -- apply bla

        
        -- · 
        -- sorry 
        -- simp at h
        -- split_ifs at h with h''
        -- simp at h
        

      -- specialize ih alpha_equiv.1 ctxt_sub h





        


-- cases M <;> simp at alpha_equiv

  -- intros Γ M N
  -- revert M Γ
  -- induction N with
  -- | Var x =>
  --   introv; intros h h'
  --   cases M <;> simp at h
  --   · rw [←h]; exact h'
  -- | App M₀ N₀ ih₁ ih₂ =>
  --   introv; intros h h'
  --   match M with
  --   | .App M₁ N₁ =>
  --     simp at h'
  --     generalize h'' : typeOf Γ M₁ = aux
  --     rw [h''] at h'
  --     match aux with
  --     | some (τ' →' σ') => 
  --       simp at h'
  --       split_ifs at h' with h'''
  --       · 

def lambda2BetaReduction : Λ2 V 𝕍 → Λ2 V 𝕍 → Prop
| .Lam x σ M, R => ∃ M', R = Λ2.Lam x σ M' ∧ lambda2BetaReduction M M'
| .TLam α M, R  => ∃ M', R = Λ2.TLam α M' ∧ lambda2BetaReduction M M'
| .App M N, R => 
    (∃ M' N' : Λ2 V 𝕍, R = M' N' ∧
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
| .TApp M σ, R => 
  (∃ M', R = Λ2.TApp M' σ ∧ lambda2BetaReduction M M') ∨
  (
    match M with
    | .TLam α M' => R = subTVarInTerm α σ M' 
    | _          => False
  )
| .Var _, _ => False

lemma varSubPreservesTypeVar 
  {Γ : TCtxt2 V 𝕍} {N : Λ2 V 𝕍} {x y : V} {σ : 𝕋2 𝕍} : (Γ ⊢ N : σ) →
    typeOf (Γ;; x : σ) (Λ2.Var y) = typeOf Γ (subVarInTerm x N (Λ2.Var y)) := by
  intro h
  simp
  split_ifs with h' h'' h''
  · rw [h]
  · exfalso; exact h'' (Eq.symm h')
  · exfalso; exact h' (Eq.symm h'')
  · simp

-- lemma varSubPreservesType {M N : Λ2 V 𝕍} {x : V} {σ : 𝕋2 𝕍} :
--     ∀ {Γ : TCtxt2 V 𝕍}, (Γ ⊢ N : σ) → typeOf (Γ;; x : σ) M = typeOf Γ (subVarInTerm x N M) := by
--   intros Γ h
--   induction M with
--   | Var y => exact varSubPreservesTypeVar h
--   | App _ _ ih₁ ih₂ => simp [ih₁, ih₂]
--   | TApp M τ ih => simp [ih]
--   | Lam y τ M ih =>
--     by_cases h' : x = y
--     · simp [h']
--       rw [ctxtTypeOfPreservation]
--       intros x _
--       exact getTypeRebind x
--     · simp [h']
      

      







    
    





   
-- lemma varSubPreservesType {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (M N : Λ2 V 𝕍) (x : V) (σ τ : 𝕋2 𝕍) :
--   (Γ ⊢ (λ' x : τ, M) N : σ) → (Γ ⊢ (subVarInTerm x N M) : σ) := by
--     intros h
--     rw [←appl_rule] at h
--     rcases h with ⟨τ', h₁, h₂⟩
--     simp at h₁
--     generalize h : typeOf (Γ;; x : τ) M = σM
--     rw [h] at h₁
--     match σM with
--     | none => simp at h₁
--     | some σ' => 
--       simp at h₁
--       rw [←h₁.1] at h₂
--       rw [h₁.2] at h
--       clear h₁
--       revert σ
--       revert Γ
--       induction M with
--       | Var y => 
--         intros Γ h₂ σ h₁; exact varSubPreservesTypeVar σ h₁ h₂
--       | App M₁ M₂ ih₁ ih₂ => 
--         intros Γ h₂ σ h₁
--         simp at h₁
--         generalize aux : typeOf (Γ;; x : τ) M₁ = σM₁
--         rw [aux] at h₁
--         match σM₁ with
--         | some (.To τ' σ') => 
--           simp at h₁
--           split_ifs at h₁ with aux'
--           · rw [Option.some.injEq] at h₁ 
--             rw [h₁] at aux
--             specialize ih₁ Γ h₂ (τ' →' σ) aux
--             specialize ih₂ Γ h₂ τ' aux'
--             simp at ih₁ ih₂
--             simp
--             rw [ih₁, ih₂]
--             simp
--       | TApp M γ ih => 
--         intros Γ h₂ σ h₁
--         simp at h₁
--         generalize aux : typeOf (Γ;; x : τ) M = σM
--         rw [aux] at h₁
--         match σM with
--         | some (Π α : *, τ') => 
--           simp at h₁
--           specialize ih Γ h₂ (Π α : *, τ') aux
--           simp at ih
--           simp [ih, h₁]
--         | some (.TVar x) => simp at h₁
--         | some (_ →' _) =>  simp at h₁
--         | none => simp at h₁ 
--       | Lam y σ' M ih =>
--         intros Γ h₂ σ h₁
--         simp at h₁
--         unfold subVarInTerm
--         split_ifs with cond
--         · simp [cond] at h₁
--           simp [←h₁, ctxtTypeOfPreservation (λ _ _ => getTypeRebind)]
--         · simp -- [←h₁]
--           have h' : 
--               ∀ (z : V), z ∈ freeVarsOfTerm M →
--                 getType z ((Γ;; x : τ);; y : σ') = getType z ((Γ;; y : σ');; x : τ) := 
--             λ _ _ => getTypeReorder cond
--           rw [ctxtTypeOfPreservation h'] at h₁

--           specialize ih (Γ;; y : σ') 
          





            

--           specialize ih (Γ;; y : σ') 


          
          

          


--       | TLam α M => sorry














notation:9 M "→ᵦ" N => lambda2BetaReduction M N 

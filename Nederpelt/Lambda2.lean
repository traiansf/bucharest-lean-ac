import Mathlib.Data.Finset.Basic


inductive 𝕋2 (𝕍 : Type) : Type
| TVar : 𝕍    → 𝕋2 𝕍
| To   : 𝕋2 𝕍 → 𝕋2 𝕍 → 𝕋2 𝕍
| TTo  : 𝕍 → 𝕋2 𝕍 → 𝕋2 𝕍
deriving DecidableEq

@[simp]
def substTVar {𝕍 : Type} [DecidableEq 𝕍] (α : 𝕍) (σ : 𝕋2 𝕍) : 𝕋2 𝕍 → 𝕋2 𝕍
| .TVar α' => 
  if α = α'
  then σ
  else .TVar α'
| .To τ τ' => .To (substTVar α σ τ) (substTVar α σ τ')
| .TTo α' τ => 
  .TTo α' (if α = α' then σ else (substTVar α σ τ))


@[simp]
def freeTVarsOfType {𝕍 : Type} [DecidableEq 𝕍] : 𝕋2 𝕍 → Finset 𝕍
| (.TVar α) => {α}
| (.To σ₁ σ₂) => (freeTVarsOfType σ₁) ∪ (freeTVarsOfType σ₂)
| (.TTo α σ) => (freeTVarsOfType σ).erase α

inductive Λ2 (V : Type) (𝕍 : Type) : Type
| Var  : V → Λ2 V 𝕍
| App  : Λ2 V 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍 
| TApp : Λ2 V 𝕍 → 𝕋2 𝕍 → Λ2 V 𝕍
| Lam  : V → 𝕋2 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍
| TLam : 𝕍 → Λ2 V 𝕍 → Λ2 V 𝕍

@[simp]
def freeVarsOfTerm {V 𝕍 : Type} [DecidableEq V] : Λ2 V 𝕍 → Finset V
| .Var x     => {x}
| .App M N   => (freeVarsOfTerm M) ∪ (freeVarsOfTerm N)
| .TApp M _  => freeVarsOfTerm M
| .Lam x _ M => (freeVarsOfTerm M).erase x
| .TLam _ M  => freeVarsOfTerm M

@[simp]
def freeTVarsOfTerm {V 𝕍 : Type} [DecidableEq 𝕍] : Λ2 V 𝕍 → Finset 𝕍
| .Var  _     => {}
| .App  M N   => (freeTVarsOfTerm M) ∪ (freeTVarsOfTerm N)
| .TApp M σ   => (freeTVarsOfTerm M) ∪ (freeTVarsOfType σ)
| .Lam  _ σ M => (freeTVarsOfTerm M) ∪ (freeTVarsOfType σ)
| .TLam α M   => (freeTVarsOfTerm M).erase α

inductive TCtxt2 (V : Type) (𝕍 : Type) : Type
| Empty       : TCtxt2 V 𝕍
| TypeVarCtxt : 𝕍 → TCtxt2 V 𝕍 → TCtxt2 V 𝕍
| VarCtxt     : V → 𝕋2 𝕍 → TCtxt2 V 𝕍 → TCtxt2 V 𝕍   

@[simp]
def TDomTCtxt {V 𝕍 : Type} [DecidableEq 𝕍] : TCtxt2 V 𝕍 → Finset 𝕍
| .Empty           => {} 
| .TypeVarCtxt α Γ => {α} ∪ (TDomTCtxt Γ)
| .VarCtxt _ _ Γ   => TDomTCtxt Γ

@[simp]
def DomTCtxt {V 𝕍 : Type} [DecidableEq V] : TCtxt2 V 𝕍 → Finset V
| .Empty           => {} 
| .TypeVarCtxt _ Γ => DomTCtxt Γ
| .VarCtxt x _ Γ   => (DomTCtxt Γ) ∪ {x}

@[simp]
def getType {V 𝕍 : Type} [DecidableEq V] (x : V) : TCtxt2 V 𝕍 → Option (𝕋2 𝕍)
| .Empty => none
| .TypeVarCtxt _ Γ => getType x Γ 
| .VarCtxt x' σ Γ => 
    if x = x'
    then some σ
    else getType x Γ

lemma typeOfDefinedOfInTCtxt {V 𝕍 : Type} [DecidableEq V] : 
  ∀ (Γ : TCtxt2 V 𝕍) (x : V), 
    x ∈ DomTCtxt Γ → (∃ σ : 𝕋2 𝕍, (getType x Γ) = (some σ)) := by
  intros Γ x;
  induction' Γ with α Γ h_ind x' σ Γ h_ind
  · simp
  · simp; assumption
  · simp;  
    by_cases h' : x = x'
    · simp [h']
    · simp [h']; assumption

def wellFormedTCtxt {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] : TCtxt2 V 𝕍 → Prop 
| .Empty => True
| .TypeVarCtxt α Γ => α ∉ TDomTCtxt Γ ∧ wellFormedTCtxt Γ
| .VarCtxt x σ Γ => x ∉ DomTCtxt Γ ∧ 
                    ∀ α : 𝕍, 
                      α ∈ freeTVarsOfType σ → 
                        α ∈ TDomTCtxt Γ ∧ 
                    wellFormedTCtxt Γ

@[simp]
def typeOf {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) : Λ2 V 𝕍 → Option (𝕋2 𝕍)
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
  | .some (.TTo α τ) => some (substTVar α σ τ)
  | _                => none
| .Lam x σ M => 
  match typeOf (.VarCtxt x σ Γ) M with 
  | .some τ => some (.To σ τ)
  | _       => none
| .TLam α M => 
  match typeOf (.TypeVarCtxt α Γ) M with
  | .some τ => some (.TTo α τ)
  | _       => none

@[simp]
def typingJudgement {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] 
    (Γ : TCtxt2 V 𝕍) (M : Λ2 V 𝕍) (σ : 𝕋2 𝕍) : Prop :=
  typeOf Γ M = some σ

def formationRule {V 𝕍 : Type} [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (σ : 𝕋2 𝕍) : Prop := freeTVarsOfType σ ⊆ TDomTCtxt Γ

notation:10 Γ " ⊢ " M " : " σ => typingJudgement Γ M σ
notation:10 Γ " ⊢ " σ " : * " => formationRule Γ σ
notation:9 σ " →' " τ => 𝕋2.To σ τ 
notation:9 Γ ";; " x " : " σ => TCtxt2.VarCtxt x σ Γ
notation:9 Γ ";; " α " : * " => TCtxt2.TypeVarCtxt α Γ

lemma var_rule {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (x : V) (σ : 𝕋2 𝕍) :
  getType x Γ = some σ → (Γ ⊢ .Var x : σ) := by simp

lemma appl_rule {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (M N : Λ2 V 𝕍) (σ τ : 𝕋2 𝕍) : 
  (Γ ⊢ M : (.To σ τ)) → (Γ ⊢ N : σ) → (Γ ⊢ (.App M N) : τ) := by
    intros h h'; unfold typingJudgement at *; simp only [typeOf, h, h', Option.some.injEq, ite_true]

lemma abst_rule {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (M : Λ2 V 𝕍) (x : V) (σ τ : 𝕋2 𝕍) :
  ((Γ;; x : σ) ⊢ M : τ) → (Γ ⊢ .Lam x σ M : σ →' τ) := by
    intros h; unfold typingJudgement at *; simp [h]

lemma appl₂_rule {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (α : 𝕍) (M : Λ2 V 𝕍) (σ τ : 𝕋2 𝕍) :
  (Γ ⊢ M : .TTo α σ) → (Γ ⊢ σ : *) → (Γ ⊢ .TApp M τ : substTVar α τ σ) := by
    intros h _; simp at *; simp [h]

lemma abst₂_rule {V 𝕍 : Type} [DecidableEq V] [DecidableEq 𝕍] (Γ : TCtxt2 V 𝕍) (α : 𝕍) (M : Λ2 V 𝕍) (σ : 𝕋2 𝕍) :
  ((Γ;; α : *) ⊢ M : σ) → (Γ ⊢ (.TLam α M) : (.TTo α σ)) := by
    intros h; unfold typingJudgement at h; simp [h]


  


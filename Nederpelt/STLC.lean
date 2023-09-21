import Mathlib.Data.Finset.Basic

set_option autoImplicit false 

inductive 𝕋 (𝕍 : Type) : Type
| TConst : 𝕍    → 𝕋 𝕍
| To   : 𝕋 𝕍 → 𝕋 𝕍 → 𝕋 𝕍3
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
def boundVarsOfTerm : Λ V 𝕍 → Finset V
| .Var x     => {}
| .App M N   => (boundVarsOfTerm M) ∪ (boundVarsOfTerm N)
| .Lam x _ M => (boundVarsOfTerm M) ∪ {x}

@[simp]
def varsOfTerm (t : Λ V 𝕍) : Finset V :=
  freeVarsOfTerm t ∪ boundVarsOfTerm t

@[simp]
def subVarInTerm (x : V) (N : Λ V 𝕍) : Λ V 𝕍 → Λ V 𝕍
| .Var x'     => if x = x'
                 then N 
                 else Λ.Var x'
| .App M M'   => Λ.App (subVarInTerm x N M) (subVarInTerm x N M')
-- | .TApp M τ   => Λ.TApp (subVarInTerm x N M) τ
| .Lam x' τ M => Λ.Lam x' τ (if x = x' then M else subVarInTerm x N M)
-- | .TLam α M   => Λ.TLam α (subVarInTerm x N M)

def var_update (var_map : V -> V) (to_replace replacement : V) (x : V) : V :=
  if x = to_replace then replacement else var_map x

@[simp]
def AlphaEquiv' (var_map₀ var_map₁ : V →  V) : Λ V 𝕍 → Λ V 𝕍 → Prop
| .Var x₀, .Var x₁ => var_map₀ x₀ = var_map₁ x₁ 
| .App M₀ M₀', .App M₁ M₁' => 
  AlphaEquiv' var_map₀ var_map₁ M₀ M₁ ∧
  AlphaEquiv' var_map₀ var_map₁ M₀' M₁'
| .Lam x₀ σ₀ M₀, .Lam x₁ σ₁ M₁ => σ₀ = σ₁ ∧ ∃ x' : V, x' ∉ (freeVarsOfTerm M₀).map var_map₀ ∪ varsOfTerm M₁ ∧
  AlphaEquiv' (var_update var_map₀ x₀ x') (var_update var_map₁ x₁ x') M₀ M₁
| _, _ => False
  
@[simp]
def AlphaEquiv (M N : Λ V 𝕍) : Prop := AlphaEquiv' id id M N


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
  | some (τ →' σ) => 
    if typeOf Γ N = some τ
    then some σ
    else none
  | _               => none
| .Lam x σ M => 
  match typeOf (.VarCtxt x σ Γ) M with 
  | some τ => some (.To σ τ)
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

lemma typeOfRebind {M : Λ V 𝕍} {Γ : TCtxt V 𝕍} {y : V} {σ σ' : 𝕋 𝕍} :
    typeOf ((Γ;; y : σ);; y : σ') M = typeOf (Γ;; y : σ') M := by
  apply ctxtTypeOfPreservation
  intros x Hx
  rw [getTypeRebind]

lemma typeOfReorder {M : Λ V 𝕍} {Γ : TCtxt V 𝕍} {x y : V} {σ σ' : 𝕋 𝕍} :
    x ≠ y → 
      typeOf ((Γ;;x : σ);; y : σ') M = typeOf ((Γ;;y : σ');; x : σ) M := by
  intros Hxy
  apply ctxtTypeOfPreservation
  intros x Hx
  rw [getTypeReorder]
  assumption
 
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
    {var_map var_map' : V → V},
      AlphaEquiv' var_map var_map' M M' →
      (∀ x x' : V, x ∈ freeVarsOfTerm M → x' ∈ freeVarsOfTerm M' →
        var_map x = var_map' x' -> getType x Γ = getType x' Γ'
      )
      → (Γ ⊢ M : σ) → (Γ' ⊢ M' : σ) := by
  intros M'
  induction M' with
  | Var y =>
    introv
    intros alpha_equiv ctxt_equiv
    match M with
    | .Var x =>
      simp at alpha_equiv ctxt_equiv |-
      intro Hx
      rewrite [<- Hx]
      symm
      apply ctxt_equiv
      assumption
  | App M₀' M₁' ih₀ ih₁ =>
    introv 
    intros alpha_equiv ctxt_equiv h
    match M with
    | .App M₀ M₁ =>
      simp at alpha_equiv ctxt_equiv |-
      rw [←appl_rule] at h
      rcases h with ⟨τ, h₀, h₁⟩
      have ctxt_equiv₀ : ∀ (x x' : V), x ∈ freeVarsOfTerm M₀ → x' ∈ freeVarsOfTerm M₀' → 
        var_map x = var_map' x' -> getType x Γ = getType x' Γ' := by
        intros x x' Hx Hx' 
        apply ctxt_equiv <;> simp <;> left <;> assumption
      have ctxt_equiv₁ : ∀ (x x' : V), x ∈ freeVarsOfTerm M₁ → x' ∈ freeVarsOfTerm M₁' → 
        var_map x = var_map' x' -> getType x Γ = getType x' Γ' := by
        intros x x' Hx Hx' 
        apply ctxt_equiv <;> simp <;> right <;> assumption
      specialize ih₀ alpha_equiv.1 ctxt_equiv₀ h₀
      specialize ih₁ alpha_equiv.2 ctxt_equiv₁ h₁
      simp
      simp at ih₀ ih₁
      simp [ih₀, ih₁]
  | Lam x' τ' M' ih =>
    introv
    intros alpha_equiv ctxt_equiv h
    match M with
    | .Var _ => contradiction
    | .App _ _ => contradiction
    | .Lam x τ M =>
      simp at alpha_equiv h ctxt_equiv |-
      generalize h' : typeOf (Γ;; x : τ) M = aux
      rw [h'] at h
      match aux with
      | none => contradiction
      | some σ' =>
        rcases alpha_equiv with ⟨Heq, x1, Hx1, alpha_equiv⟩ 
        simp at h
        subst τ' σ
        simp
        have ctxt_equiv' : 
         ∀ (y y' : V), y ∈ freeVarsOfTerm M → y' ∈ freeVarsOfTerm M' →
           var_update var_map x x1 y = var_update var_map' x' x1 y' → getType y (Γ;; x : τ) = getType y' (Γ';; x' : τ) := by 
          intros y y' Hy Hy' Hupdate
          by_cases h : y = x
          . subst y
            have h' : y' = x' := by
              unfold var_update at Hupdate
              simp at Hupdate


          simp [h]
          . simp [h]
            rcases alpha_equiv with ⟨alpha_equiv, Heq⟩
            rcases ctxt_equiv y h Hy with ⟨Hy1, Hy2⟩ | ⟨y', Hy1, Hy2⟩
            . left
              constructor
              . assumption
              . split_ifs
                . sorry
                . assumption
            . right
              use y'
              constructor
              . assumption
              . split_ifs
                . sorry
                . assumption
        sorry

lemma AlphaEquivPreservesType :
  ∀ {M M' : Λ V 𝕍} {Γ : TCtxt V 𝕍} {σ : 𝕋 𝕍},
      (M =ₐ M') → (Γ ⊢ M : σ) → (Γ ⊢ M' : σ) := by
  introv; intro h h'
  exact AlphaEquivPreservesType' h (by introv; simp) h'

def substitutible (N M : Λ V 𝕍) : Prop :=
  ∀ x, x ∈ boundVarsOfTerm M → x ∉ freeVarsOfTerm N

lemma substitutible_app_l : forall M N P : Λ V 𝕍, 
  substitutible M (.App N P) -> substitutible M N := by
  intros M N P Hsub x Hx
  apply Hsub
  simp
  left
  assumption

lemma substitutible_app_r : forall M N P : Λ V 𝕍, 
  substitutible M (.App N P) -> substitutible M P := by
  intros M N P Hsub x Hx
  apply Hsub
  simp
  right
  assumption

lemma substitutible_lam : forall (M N : Λ V 𝕍) x σ, 
  substitutible M (.Lam x σ N) -> substitutible M N := by
  intros M N x σ Hsub x' Hx'
  apply Hsub
  simp
  left
  assumption

def lambda2BetaReduction : Λ V 𝕍 → Λ V 𝕍 → Prop
| .Lam x σ M, R => ∃ M', R = Λ.Lam x σ M' ∧ lambda2BetaReduction M M'
| .App M N, R => 
    (∃ M' N' : Λ V 𝕍, R = M' N' ∧
      (
        (lambda2BetaReduction M M' ∧ N' = N) ∨
        (lambda2BetaReduction N N' ∧ M' = M)
      )
    ) ∨
    (∃ M', (M =ₐ M') ∧ substitutible N M' ∧
      match M' with
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
    substitutible N M ->
    ∀ {Γ : TCtxt V 𝕍}, (Γ ⊢ N : σ) → typeOf (Γ;; x : σ) M = typeOf Γ (subVarInTerm x N M) := by
  induction M with
  | Var y =>
    intros Hsub Γ HN
    simp
    by_cases h' : x = y
    . simp [h']
      apply Eq.symm
      exact HN
    . simp [h']
      intros Hc
      apply False.elim
      apply h'
      rw [Hc]
  | App M' N' IHM' IHN' =>
    intros Hsub Γ HN
    simp
    rw [IHM', IHN']
    . apply substitutible_app_r
      assumption
    . assumption
    . apply substitutible_app_l
      assumption
    . assumption
  | Lam y τ M' IHM' =>
    intros Hsubst Γ HN
    simp
    split_ifs with h
    . rw [h, typeOfRebind]
    . rw [typeOfReorder, IHM']
      . apply substitutible_lam
        assumption
      . unfold typingJudgement
        rewrite [<- HN]
        apply ctxtTypeOfPreservation
        intros t Ht
        simp
        intros Hty
        apply False.elim
        apply Hsubst t
        . simp
          right
          assumption
        . assumption
      . assumption

theorem betaReductionPreservesType {Γ : TCtxt V 𝕍} {M M' : Λ V 𝕍} {σ : 𝕋 𝕍} :
  (M ↠ M') → (Γ ⊢ M : σ) → (Γ ⊢ M' : σ) := by
  revert Γ M' σ
  induction M <;> intros Γ M' σ Hbeta HM
  case Var => contradiction
  case Lam x τ Mx IHMx =>
    rcases Hbeta with ⟨Mx', HMx', Hbeta⟩
    subst M'
    simp
    simp at HM
    generalize h' : typeOf (Γ;; x : τ) Mx = υ; rw [h'] at HM
    rcases υ with none | υ
    . contradiction
    . simp at HM
      subst σ
      specialize IHMx Hbeta h'
      rw [IHMx]
  case App  M N IHM IHN =>
    rcases Hbeta with ⟨M1, N1, Heq, ⟨Hbeta,Heq'⟩ | ⟨Hbeta,Heq'⟩⟩ | ⟨M1, Halpha, ⟨Hsubst, Hbeta⟩⟩
    . subst N1 M'
      simp at HM |-
      generalize h' : typeOf Γ M = υ; rw [h'] at HM
      rcases υ with none | υ
      . contradiction
      . rcases υ with x | ⟨τ',σ'⟩
        . contradiction
        . simp at HM
          specialize IHM Hbeta h'
          rw [IHM]
          assumption
    . subst M1 M'
      simp at HM |-
      generalize HtM : typeOf Γ M = tM; rw [HtM] at HM
      rcases tM with none | tM
      . contradiction
      . rcases tM with x | ⟨τ',σ'⟩
        . contradiction
        . simp at HM |-
          split_ifs at HM with HtN ; simp at HM
          subst σ'
          specialize IHN Hbeta HtN
          rw [IHN]
          simp
    . rcases M1 with _ | _ | ⟨x,σx,Mx⟩ <;> simp at Hbeta
      subst M'
      simp at HM |-
      generalize HtM : typeOf Γ M = tM; rw [HtM] at HM
      rcases tM with none | tM
      . contradiction
      . rcases tM with x | ⟨τ',σ'⟩
        . contradiction
        . simp at HM
          have HtM' := AlphaEquivPreservesType Halpha HtM
          simp at HtM'
          generalize HtMx : typeOf (Γ;; x : σx) Mx = tMx; rw [HtMx] at HtM'
          rcases tMx with none | tMx
          . contradiction
          . simp at HtM'
            rcases HtM'
            subst τ' σ'
            split_ifs at HM with HtN ; simp at HM
            subst tMx
            rewrite [<- HtMx]
            symm
            apply varSubPreservesType
            . apply substitutible_lam
              assumption
            . assumption

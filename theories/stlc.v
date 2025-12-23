From Stdlib Require Import Utf8.
From Stdlib Require Import List.
From Autosubst Require Import Autosubst.
From stdpp Require Import relations.

(* relations *)

Inductive typ :=
| Bool : typ
| Arr : typ → typ → typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Bind Scope typ_scope with typ.

Inductive exp :=
| Var : var → exp
| BLit : bool → exp
| Abs : typ → {bind exp} → exp
| App : exp → exp → exp.

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Bind Scope exp_scope with exp.

#[export] Instance Ids_exp : Ids exp. derive. Defined.
#[export] Instance Rename_exp : Rename exp. derive. Defined.
#[export] Instance Subst_exp : Subst exp. derive. Defined.
#[export] Instance SubstLemmas_exp : SubstLemmas exp. derive. Qed.

Coercion Var : var >-> exp.
Coercion BLit : bool >-> exp.

Definition ctx := list typ.
Notation "∅" := nil.

Implicit Types
  (e v : exp)
  (x : var)
  (b : bool)
  (Γ : ctx)
  (σ : var → exp).

Inductive val : exp → Prop :=
| ValBool : ∀ b, val b
| ValArr : ∀ τ e, val (Abs τ e).

#[export]
Hint Constructors typ exp val : core.

(* Operational Semantics *)

Reserved Infix "↪" (at level 70).
Inductive step : exp → exp → Prop :=
| StepBeta : ∀ τ e v,
    val v →
    (App (Abs τ e) v) ↪ e.[v/]
| StepApp₁ : ∀ e₁ e₁' e₂,
    e₁ ↪ e₁' →
    App e₁ e₂ ↪ App e₁' e₂
| StepApp₂ : ∀ e₁ e₂ e₂',
    val e₁ →
    e₂ ↪ e₂' →
    App e₁ e₂ ↪ App e₁ e₂'
where "e ↪ e'" := (step e e').

Infix "↪*" := (rtc step) (at level 70).

#[export]
Hint Constructors step rtc : core.

(* Syntactic Typing *)

Reserved Notation "Γ ∋ x : τ" (at level 65, x at next level).
Inductive lookup : ctx → var → typ → Prop :=
| LookupZero : ∀ τ Γ,
    τ :: Γ ∋ 0 : τ
| LookupSucc : ∀ Γ τ₁ x τ₂,
    Γ ∋ x : τ₂ →
    τ₁ :: Γ ∋ S x : τ₂
where "Γ ∋ x : τ" := (lookup Γ x τ).

Reserved Notation "Γ ⊢ e : τ" (at level 65, e at next level).
Inductive typing : ctx → exp → typ → Prop :=
| TypingVar : ∀ Γ x τ,
    Γ ∋ x : τ →
    Γ ⊢ x : τ
| TypingBLit : ∀ Γ b,
    Γ ⊢ b : Bool
| TypingAbs : ∀ Γ τ₁ e τ₂,
    τ₁ :: Γ ⊢ e : τ₂ →
    Γ ⊢ Abs τ₁ e : Arr τ₁ τ₂
| TypingApp : ∀ Γ τ₁ τ₂ e₁ e₂,
    Γ ⊢ e₁ : Arr τ₁ τ₂ →
    Γ ⊢ e₂ : τ₁ →
    Γ ⊢ App e₁ e₂ : τ₂
where "Γ ⊢ e : τ" := (typing Γ e τ).

#[export]
Hint Constructors lookup typing : core.

(* Semantic Typing *)

Inductive blit_val : exp → Prop :=
| BLitValBLit : ∀ b, blit_val b.

Inductive abs_val : exp → Prop :=
| AbsValAbs : ∀ τ e, abs_val (Abs τ e).

#[export]
Hint Constructors blit_val abs_val : core.

Reserved Notation "e ∈ 𝒱⟦ τ ⟧".
Fixpoint val_rel e τ : Prop :=
  match τ with
  | Bool => blit_val e
  | Arr τ₁ τ₂ => abs_val e ∧ ∀ v,
      v ∈ 𝒱⟦τ₁⟧ →
      (∃ v',
        App e v ↪* v' ∧ v' ∈ 𝒱⟦τ₂⟧)
  end
where "e ∈ 𝒱⟦ τ ⟧" := (val_rel e τ).

Reserved Notation "σ ∈ 𝒢⟦ Γ ⟧".
Inductive ctx_rel : (var → exp) → ctx → Prop :=
| CtxRelNil : ids ∈ 𝒢⟦∅⟧
| CtxRelCons : ∀ Γ σ τ v,
    σ ∈ 𝒢⟦Γ⟧ →
    v ∈ 𝒱⟦τ⟧ →
    (v .: σ) ∈ 𝒢⟦τ :: Γ⟧
where "σ ∈ 𝒢⟦ Γ ⟧" := (ctx_rel σ Γ).

#[export]
Hint Constructors ctx_rel : core.

Definition exp_rel e τ : Prop :=
  ∃ v,
  e ↪* v ∧ v ∈ 𝒱⟦τ⟧.
Notation "e ∈ ℰ⟦ τ ⟧" := (exp_rel e τ).

Definition sem_typing Γ e τ :=
  ∀ σ,
  σ ∈ 𝒢⟦Γ⟧ →
  e.[σ] ∈ ℰ⟦τ⟧.
Notation "Γ ⊨ e : τ" := (sem_typing Γ e τ) (at level 65, e at next level).

(* Fundamental Property *)

Lemma ctx_rel_lookup_msubst_val_rel : ∀ Γ σ x τ,
  σ ∈ 𝒢⟦Γ⟧ →
  Γ ∋ x : τ →
  σ x ∈ 𝒱⟦τ⟧.
Proof with eauto.
  intros.
  generalize dependent x.
  generalize dependent τ.
  induction H; intros.
  - inversion H0.
  - inversion H1; subst...
Qed.

Lemma fundamental_property_var : ∀ Γ x τ,
  Γ ∋ x : τ →
  Γ ⊨ x : τ.
Proof with eauto.
  unfold sem_typing.
  intros.
  exists (σ x).
  split...
  eapply ctx_rel_lookup_msubst_val_rel...
Qed.

Lemma fundamental_property_blit : ∀ Γ b,
  Γ ⊨ b : Bool.
Proof with auto.
  intros.
  exists b.
  split; simpl...
Qed.

Lemma val_rel_val : ∀ τ v,
  v ∈ 𝒱⟦τ⟧ →
  val v.
Proof with eauto.
  induction τ; intros; destruct H; subst...
  inversion H...
Qed.

Lemma fundamental_property_abs : ∀ Γ τ₁ e τ₂,
  τ₁ :: Γ ⊨ e : τ₂ →
  Γ ⊨ Abs τ₁ e : Arr τ₁ τ₂.
Proof with eauto.
  unfold sem_typing.
  intros.
  exists ((Abs τ₁ e).[σ]).
  repeat split...
  intros.
  specialize H with (v .: σ).
  enough (e.[v .: σ] ∈ ℰ⟦τ₂⟧)...
  unfold exp_rel in H2.
  destruct H2 as [v0 [Hstep_v0 Hvrel_v0]].
  exists v0.
  split...
  apply rtc_l with (y := e.[up σ].[v/]).
  - apply StepBeta.
    eapply val_rel_val...
  - asimpl...
Qed.

Lemma fundamental_property_app : ∀ Γ τ₁ τ₂ e₁ e₂,
  Γ ⊨ e₁ : Arr τ₁ τ₂ →
  Γ ⊨ e₂ : τ₁ →
  Γ ⊨ App e₁ e₂ : τ₂.
Proof with eauto.
  unfold sem_typing.
  unfold exp_rel.
  intros.
  specialize (H σ H1).
  specialize (H0 σ H1).
  destruct H as [v1 [Hmsubst_v1 Hvrel_v1]].
  destruct H0 as [v2 [Hmsubst_v2 Hvrel_v2]].
  destruct Hvrel_v1 as [Haval_v1 Happ_v1].
  specialize (Happ_v1 v2 Hvrel_v2).
  destruct Happ_v1 as [v [Hmstep_v Hvrel_v]].
  exists v.
  split...
  inversion Haval_v1; subst.
  simpl.
  apply rtc_trans with (y := App (Abs τ e) v2)...
  apply rtc_trans with (y := App (Abs τ e) e₂.[σ])...
  - induction Hmsubst_v1...
  - induction Hmsubst_v2...
Qed.

Theorem fundamental_property : ∀ Γ e τ,
  Γ ⊢ e : τ →
  Γ ⊨ e : τ.
Proof with eauto.
  intros.
  induction H.
  - apply fundamental_property_var...
  - apply fundamental_property_blit.
  - apply fundamental_property_abs...
  - eapply fundamental_property_app...
Qed.

From Stdlib Require Import Utf8.
From Stdlib Require Import List.
From Autosubst Require Import Autosubst.

(* STLC *)

Inductive typ :=
| typ_bool : typ
| typ_arr : typ → typ → typ.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.
Bind Scope typ_scope with typ.
Notation "'𝔹'" := typ_bool : typ_scope.
Infix "→" := typ_arr : typ_scope.

Inductive exp :=
| exp_var : var → exp
| exp_blit : bool → exp
| exp_abs : typ → {bind exp} → exp
| exp_app : exp → exp → exp.

Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Bind Scope exp_scope with exp.
Notation "'ƛ' τ , e" := (exp_abs τ e) (at level 71) : exp_scope.
Notation "e₁ [ e₂ ]" := (exp_app e₁ e₂) (at level 68, left associativity) : exp_scope.

#[export] Instance Ids_exp : Ids exp. derive. Defined.
#[export] Instance Rename_exp : Rename exp. derive. Defined.
#[export] Instance Subst_exp : Subst exp. derive. Defined.
#[export] Instance SubstLemmas_exp : SubstLemmas exp. derive. Qed.

Coercion exp_var : var >-> exp.
Coercion exp_blit : bool >-> exp.

Definition ctx := list typ.
Notation "∅" := nil.

Implicit Types
  (e v : exp)
  (x : var)
  (b : bool)
  (Γ : ctx)
  (σ : var → exp).

Inductive val : exp → Prop :=
| val_bool : ∀ b, val b
| val_arr : ∀ τ e, val (ƛ τ, e).

#[export]
Hint Constructors typ exp val : core.

(* Operational Semantics *)

Reserved Infix "↪" (at level 70).
Inductive red : exp → exp → Prop :=
| red_beta : ∀ τ e v,
    val v →
    (ƛ τ, e) [v] ↪ e.[v/]
| red_app₁ : ∀ e₁ e₁' e₂,
    e₁ ↪ e₁' →
    e₁ [e₂] ↪ e₁' [e₂]
| red_app₂ : ∀ e₁ e₂ e₂',
    val e₁ →
    e₂ ↪ e₂' →
    e₁ [e₂] ↪ e₁ [e₂']
where "e ↪ e'" := (red e e').

Reserved Infix "↪*" (at level 70).
Inductive mred : exp → exp → Prop :=
| mred_base : ∀ e, e ↪* e
| mred_step : ∀ e e' e'',
    e ↪ e' →
    e' ↪* e'' →
    e ↪* e''
where "e ↪* e'" := (mred e e').

#[export]
Hint Constructors red mred : core.

Lemma mred_refl : ∀ e,
  e ↪* e.
Proof.
  auto.
Qed.

Lemma mred_trans : ∀ e e' e'',
  e ↪* e' →
  e' ↪* e'' →
  e ↪* e''.
Proof with eauto.
  intros.
  induction H...
Qed.

(* Syntactic Typing *)

Reserved Notation "Γ ∋ x : τ" (at level 65, x at next level).
Inductive lookup : ctx → var → typ → Prop :=
| lookup_zero : ∀ τ Γ,
    τ :: Γ ∋ 0 : τ
| lookup_succ : ∀ Γ τ₁ x τ₂,
    Γ ∋ x : τ₂ →
    τ₁ :: Γ ∋ S x : τ₂
where "Γ ∋ x : τ" := (lookup Γ x τ).

Reserved Notation "Γ ⊢ e : τ" (at level 65, e at next level).
Inductive typing : ctx → exp → typ → Prop :=
| typing_var : ∀ Γ x τ,
    Γ ∋ x : τ →
    Γ ⊢ x : τ
| typing_blit : ∀ Γ b,
    Γ ⊢ b : 𝔹
| typing_abs : ∀ Γ τ₁ e τ₂,
    τ₁ :: Γ ⊢ e : τ₂ →
    Γ ⊢ (ƛ τ₁, e) : (τ₁ → τ₂)
| typing_app : ∀ Γ τ₁ τ₂ e₁ e₂,
    Γ ⊢ e₁ : (τ₁ → τ₂) →
    Γ ⊢ e₂ : τ₁ →
    Γ ⊢ (e₁ [e₂]) : τ₂
where "Γ ⊢ e : τ" := (typing Γ e τ).

#[export]
Hint Constructors lookup typing : core.

(* Semantic Typing *)

Inductive blit_val : exp → Prop :=
| blit_val_blit : ∀ b, blit_val b.

Inductive abs_val : exp → Prop :=
| abs_val_abs : ∀ τ e, abs_val (ƛ τ, e).

#[export]
Hint Constructors blit_val abs_val : core.

Reserved Notation "e ∈ 𝒱⟦ τ ⟧".
Fixpoint val_rel e τ : Prop :=
  match τ with
  | typ_bool => blit_val e
  | typ_arr τ₁ τ₂ => abs_val e ∧ ∀ v,
      v ∈ 𝒱⟦τ₁⟧ →
      (∃ v',
        (e [v]) ↪* v' ∧ v' ∈ 𝒱⟦τ₂⟧)
  end
where "e ∈ 𝒱⟦ τ ⟧" := (val_rel e τ).

Reserved Notation "σ ∈ 𝒢⟦ Γ ⟧".
Inductive ctx_rel : (var → exp) → ctx → Prop :=
| ctx_rel_nil : ids ∈ 𝒢⟦∅⟧
| ctx_rel_cons : ∀ Γ σ τ v,
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
  (σ x) ∈ 𝒱⟦τ⟧.
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
  Γ ⊨ b : 𝔹.
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
  Γ ⊨ (ƛ τ₁, e) : (τ₁ → τ₂).
Proof with eauto.
  unfold sem_typing.
  intros.
  exists ((ƛ τ₁, e)%exp.[σ]).
  repeat split...
  intros.
  specialize H with (v .: σ).
  enough (e.[v .: σ] ∈ ℰ⟦τ₂⟧)...
  unfold exp_rel in H2.
  destruct H2 as [v0 [Hred_v0 Hvrel_v0]].
  exists v0.
  split...
  apply mred_step with (e' := e.[up σ].[v/]).
  - apply red_beta.
    eapply val_rel_val...
  - asimpl...
Qed.

Lemma fundamental_property_app : ∀ Γ τ₁ τ₂ e₁ e₂,
  Γ ⊨ e₁ : (τ₁ → τ₂) →
  Γ ⊨ e₂ : τ₁ →
  Γ ⊨ (e₁ [e₂]) : τ₂.
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
  destruct Happ_v1 as [v [Hmred_v Hvrel_v]].
  exists v.
  split...
  inversion Haval_v1; subst.
  simpl.
  apply mred_trans with (e' := ((ƛ τ, e) [v2])%exp)...
  apply mred_trans with (e' := ((ƛ τ, e) [e₂.[σ]])%exp)...
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
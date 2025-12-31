From Stdlib Require Import List Utf8.
From Autosubst Require Import Autosubst.
From Equations Require Import Equations.
From stdpp Require Import relations (rtc(..), rtc_trans).
From Hammer Require Import Tactics.
From Corelib Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* STLC *)

Implicit Types
  (x : var)
  (b : bool).

Inductive typ :=
| Bool
| Arr (τ₁ τ₂ : typ).

Implicit Types
  (τ :typ).

Inductive exp :=
| Var x
| BLit b
| Abs τ (e : {bind exp})
| App (e₁ e₂ : exp).

Coercion Var : var >-> exp.
Coercion BLit : bool >-> exp.

Definition ctx := list typ.
Notation "∅" := nil.

Implicit Types
  (e v : exp)
  (Γ : ctx)
  (σ : var → exp).

Inductive val : exp → Prop :=
| ValBool : ∀ b, val b
| ValArr : ∀ τ e, val (Abs τ e).

#[export]
Hint Constructors typ exp val : core.

(* Autosubst *)

#[export] Instance Ids_exp : Ids exp. derive. Defined.
#[export] Instance Rename_exp : Rename exp. derive. Defined.
#[export] Instance Subst_exp : Subst exp. derive. Defined.
#[export] Instance SubstLemmas_exp : SubstLemmas exp. derive. Qed.

(* Operational Semantics *)

Reserved Infix "↪" (at level 70).
Inductive step : exp → exp → Prop :=
| StepBeta τ e v :
    val v →
    (App (Abs τ e) v) ↪ e.[v/]
| StepApp₁ e₁ e₁' e₂ :
    e₁ ↪ e₁' →
    App e₁ e₂ ↪ App e₁' e₂
| StepApp₂ e₁ e₂ e₂' :
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
| LookupZero τ Γ :
    τ :: Γ ∋ 0 : τ
| LookupSucc Γ τ₁ x τ₂ :
    Γ ∋ x : τ₂ →
    τ₁ :: Γ ∋ S x : τ₂
where "Γ ∋ x : τ" := (lookup Γ x τ).

Reserved Notation "Γ ⊢ e : τ" (at level 65, e at next level).
Inductive typing : ctx → exp → typ → Prop :=
| TypingVar Γ x τ :
    Γ ∋ x : τ →
    Γ ⊢ x : τ
| TypingBLit Γ b :
    Γ ⊢ b : Bool
| TypingAbs Γ τ₁ e τ₂ :
    τ₁ :: Γ ⊢ e : τ₂ →
    Γ ⊢ Abs τ₁ e : Arr τ₁ τ₂
| TypingApp Γ τ₁ τ₂ e₁ e₂ :
    Γ ⊢ e₁ : Arr τ₁ τ₂ →
    Γ ⊢ e₂ : τ₁ →
    Γ ⊢ App e₁ e₂ : τ₂
where "Γ ⊢ e : τ" := (typing Γ e τ).

#[export]
Hint Constructors lookup typing : core.

(* Semantic Typing *)

Inductive blit_val : exp → Prop :=
| BLitValBLit b : blit_val b.

Inductive abs_val : exp → Prop :=
| AbsValAbs τ e : abs_val (Abs τ e).

#[export]
Hint Constructors blit_val abs_val : core.

Reserved Notation "e ∈ 𝒱⟦ τ ⟧".
Equations val_rel e τ : Prop := {
| e, Bool := blit_val e;
| e, (Arr τ₁ τ₂) := abs_val e ∧ ∀ v,
    v ∈ 𝒱⟦τ₁⟧ →
    (∃ v', App e v ↪* v' ∧ v' ∈ 𝒱⟦τ₂⟧)
} where "e ∈ 𝒱⟦ τ ⟧" := (val_rel e τ).

Reserved Notation "σ ∈ 𝒢⟦ Γ ⟧".
Inductive ctx_rel : (var → exp) → ctx → Prop :=
| CtxRelNil : ids ∈ 𝒢⟦∅⟧
| CtxRelCons Γ σ τ v :
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

Lemma fundamental_property_var Γ x τ :
  Γ ∋ x : τ →
  Γ ⊨ x : τ.
Proof.
  rewrite/sem_typing=> Hlookup σ Hcrel.
  exists (σ x).
  split=> //.
  move: x τ Hlookup.
  by elim: Hcrel; sauto lq: on.
Qed.

Lemma fundamental_property_blit Γ b :
  Γ ⊨ b : Bool.
Proof.
  by hauto l: on.
Qed.

Lemma val_rel_val τ v :
  v ∈ 𝒱⟦τ⟧ →
  val v.
Proof.
  by elim: τ; sauto q: on.
Qed.

Lemma fundamental_property_abs Γ τ₁ e τ₂ :
  τ₁ :: Γ ⊨ e : τ₂ →
  Γ ⊨ Abs τ₁ e : Arr τ₁ τ₂.
Proof.
  rewrite/sem_typing=> Hsem_typing σ Hcrel.
  exists ((Abs τ₁ e).[σ]).
  repeat split=> //.
  move=> v Hvrel.
  move: Hsem_typing => /(_ (v .: σ)) Hsem_typing.
  have [v0 [Hstep_v0 Hvrel_v0]] : e.[v .: σ] ∈ ℰ⟦τ₂⟧ by auto.
  exists v0.
  split=> //.
  apply rtc_l with (y := e.[up σ].[v/]).
  - by eauto using StepBeta, val_rel_val.
  - by asimpl.
Qed.

Lemma fundamental_property_app Γ τ₁ τ₂ e₁ e₂ :
  Γ ⊨ e₁ : Arr τ₁ τ₂ →
  Γ ⊨ e₂ : τ₁ →
  Γ ⊨ App e₁ e₂ : τ₂.
Proof.
  rewrite/sem_typing/exp_rel=> + + σ Hcrel.
  move=> /(_ σ Hcrel) [v1 [Hmsubst_v1 [Haval_v1 Happ_v1]]].
  move=> /(_ σ Hcrel) [v2 [Hmsubst_v2 Hvrel_v2]].
  move: Happ_v1 => /(_ v2 Hvrel_v2) [v [Hmstep_v Hvrel_v]].
  exists v.
  split=> //.
  inversion Haval_v1; subst.
  apply rtc_trans with (y := App (Abs τ e) v2) => //.
  apply rtc_trans with (y := App (Abs τ e) e₂.[σ]); simpl.
  - by elim: Hmsubst_v1; eauto.
  - by elim: Hmsubst_v2; eauto.
Qed.

Theorem fundamental_property Γ e τ :
  Γ ⊢ e : τ →
  Γ ⊨ e : τ.
Proof.
  move=> H.
  induction H.
  - exact: fundamental_property_var.
  - exact: fundamental_property_blit.
  - exact: fundamental_property_abs.
  - by apply: fundamental_property_app; eauto.
Qed.

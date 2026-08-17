import Mathlib


import Lama.Semantics.Eval

namespace Lama.Semantics

open Lama.Ast

theorem Eval_unique (st : State) (e : Expr)
                    (r₁ r₂ : Result Value)
                    (h₁ : Eval st e r₁) (h₂ : Eval st e r₂)
: r₁ = r₂ := by
  induction h₁
  using Eval.rec (motive_2 := fun st es r₁ h₁ => (r₂ : Result (List RValue)) -> EvalList st es r₂ -> r₁ = r₂)
  generalizing r₂
  with
  | skip => cases h₂; simp
  | varOk st st' x y h₁ =>
    cases h₂ with
    | varOk _ st'' _ y' h₂ =>
      rw [h₁] at h₂
      simp at h₂
      obtain ⟨ rfl, rfl ⟩ := h₂
      simp
    | varErr _ _ e h₂ =>
      rw [h₁] at h₂
      simp at h₂
  | varErr st x e h₁ =>
    cases h₂ with
    | varOk _ st'' _ y' h₂ =>
      rw [h₁] at h₂
      simp at h₂
    | varErr _ _ e h₂ =>
      rw [h₁] at h₂
      simp at h₂
      obtain ⟨ rfl, rfl ⟩ := h₂
      simp
  | refOk st x h₁ =>
    cases h₂ with
    | refOk => simp
    | refErr _ _ _ h₂ => simp [h₁] at h₂
  | refErr st x e h₁ =>
    cases h₂ with
    | refOk _ _ h₂ => simp [h₁] at h₂
    | refErr _ _ e' h₂ =>
      rw [h₁] at h₂
      simp at h₂
      simp [h₂]
  | int => cases h₂; simp
  | str st st' s box h₁ =>
    cases h₂ with
    | str _ _ _ _ h₂ =>
      rw [h₁] at h₂
      simp at h₂
      obtain ⟨ rfl, rfl ⟩ := h₂
      simp
  | arrOk st₁ st₂ st₃ xs ys box h₁ h₂ ih =>
    cases h₂ with
    | arrOk _ st₂' st₃' _ ys' box' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
      obtain ⟨ rfl, rfl ⟩ := ih
      rw [h₂] at h₄
      simp at h₄
      obtain ⟨ rfl, rfl ⟩ := h₄
      simp
    | arrErr _ _ e h₃ =>
      specialize ih _ h₃
      simp at ih
  | arrErr st xs e h₁ ih =>
    cases h₂ with
    | arrOk _ st₂' st₃' _ ys' box' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
    | arrErr _ _ e h₃ =>
      specialize ih _ h₃
      simp at ih
      obtain ⟨ rfl, rfl ⟩ := ih
      simp
  | sexpOk st₁ st₂ st₃ t xs ys box h₁ h₂ ih =>
    cases h₂ with
    | sexpOk _ st₂' st₃' _ _ ys' box' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
      obtain ⟨ rfl, rfl ⟩ := ih
      rw [h₂] at h₄
      simp at h₄
      obtain ⟨ rfl, rfl ⟩ := h₄
      simp
    | sexpErr _ _ _ e h₃ =>
      specialize ih _ h₃
      simp at ih
  | sexpErr st t xs e h₁ ih =>
    cases h₂ with
    | sexpOk _ st₂' st₃' _ _ ys' box' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
    | sexpErr _ _ _ e h₃ =>
      specialize ih _ h₃
      simp at ih
      obtain ⟨ rfl, rfl ⟩ := ih
      simp
  | lambdaOk st st' xs x box env h₁ h₂ =>
    cases h₂ with
    | lambdaOk _ _ _ _ _ _ h₃ h₄ =>
      rw [h₁] at h₃
      simp at h₃
      obtain ⟨ rfl, rfl ⟩ := h₃
      rw [h₂] at h₄
      simp at h₄
      obtain ⟨ rfl, rfl ⟩ := h₄
      simp
    | lambdaErr _ _ _ h₃ =>
      rw [h₁] at h₃
      simp at h₃
  | lambdaErr st xs x h₁ =>
    cases h₂ with
    | lambdaOk _ _ _ _ _ _ h₃ _ =>
      rw [h₁] at h₃
      simp at h₃
    | lambdaErr _ _ _ _ => simp
  | binopOk st₁ st₂ st₃ op x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | binopOk _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | binopErr _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | binopErrL _ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | binopErrR _ _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | binopErr st₁ st₂ st₃ op x₁ x₂ y₁ y₂ e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | binopOk _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | binopErr _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | binopErrL _ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | binopErrR _ _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | binopErrL st op x₁ x₂ e h₁ ih =>
    cases h₂ with
    | binopOk _ _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | binopErr _ _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | binopErrL _ _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | binopErrR _ _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | binopErrR st st' op x₁ x₂ y₁ e h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | binopOk _ _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | binopErr _ _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | binopErrL _ _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | binopErrR _ _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
  | elemOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | elemOk _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | elemErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | elemErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | elemErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | elemErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | elemOk _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | elemErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | elemErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | elemErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | elemErrL st x₁ x₂ e h₁ ih =>
    cases h₂ with
    | elemOk _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | elemErr _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | elemErrL _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | elemErrR _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | elemErrR st st' x₁ x₂ y₁ e h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | elemOk _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | elemErr _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | elemErrL _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | elemErrR _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
  | elemRefOk st₁ st₂ st₃ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | elemRefOk _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | elemRefErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | elemRefErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | elemRefErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | elemRefErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | elemRefOk _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | elemRefErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | elemRefErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | elemRefErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | elemRefErrL st x₁ x₂ e h₁ ih =>
    cases h₂ with
    | elemRefOk _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | elemRefErr _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | elemRefErrL _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | elemRefErrR _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | elemRefErrR st st' x₁ x₂ y₁ e h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | elemRefOk _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | elemRefErr _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | elemRefErrL _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | elemRefErrR _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
  | callOk st₁ st₂ st₃ st₄ st₅ x xs y ys z₁ z₂ h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | callOk _ st₂' st₃' st₄' st₅' _ _ y' ys' z₁' z₂' h₅ h₆ h₇ h₈ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
      obtain ⟨ rfl, rfl ⟩ := h₇
      specialize ih₃ _ h₈
      simp at ih₃
      obtain ⟨ rfl, rfl ⟩ := ih₃
      simp
    | callErr₁ _ _ _ _ h₅ =>
      specialize ih₁ _ h₅
      simp at ih₁
    | callErr₂ _ _ _ _ _ _ h₅ h₆ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
    | callErr₃ _ _ _ _ _ _ _ _ h₅ h₆ h₇ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
    | callErr₄ _ _ _ _ _ _ _ _ _ _ h₅ h₆ h₇ h₈ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
      obtain ⟨ rfl, rfl ⟩ := h₇
      specialize ih₃ _ h₈
      simp at ih₃
  | callErr₁ st x xs e h₁ ih =>
    cases h₂ with
    | callOk _ _ _ _ _ _ _ _ _ _ _ h₃ _ _ _ =>
      specialize ih _ h₃
      simp at ih
    | callErr₁ _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | callErr₂ _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
    | callErr₃ _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | callErr₄ _ _ _ _ _ _ _ _ _ _ h₃ _ _ _ =>
      specialize ih _ h₃
      simp at ih
  | callErr₂ st st' x xs y e h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | callOk _ _ _ _ _ _ _ _ _ _ _ h₃ h₄ _ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | callErr₁ _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | callErr₂ _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
    | callErr₃ _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | callErr₄ _ _ _ _ _ _ _ _ _ _ h₃ h₄ _ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
  | callErr₃ st₁ st₂ st₃ x xs y ys e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | callOk _ _ _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ _ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | callErr₁ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | callErr₂ _ _ _ _ _ _ h₄ _ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ ‹_›
      simp at ih₂
    | callErr₃ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | callErr₄ _ _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ _ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
  | callErr₄ st₁ st₂ st₃ st₄ x xs y ys z e h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | callOk _ _ _ _ _ _ _ _ _ _ _ h₅ h₆ h₇ h₈ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
      obtain ⟨ rfl, rfl ⟩ := h₇
      specialize ih₃ _ h₈
      simp at ih₃
    | callErr₁ _ _ _ _ h₅ =>
      specialize ih₁ _ h₅
      simp at ih₁
    | callErr₂ _ _ _ _ _ _ h₅ _ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ ‹_›
      simp at ih₂
    | callErr₃ _ _ _ _ _ _ _ _ h₅ h₆ h₇ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
    | callErr₄ _ _ _ _ _ _ _ _ _ _ h₅ h₆ h₇ h₈ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₇
      simp at h₇
      obtain ⟨ rfl, rfl ⟩ := h₇
      specialize ih₃ _ h₈
      simp at ih₃
      obtain ⟨ rfl, rfl ⟩ := ih₃
      simp
  | assignOk st₁ st₂ st₃ st₄ x₁ x₂ y₁ y₂ z h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | assignOk _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | assignErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | assignErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | assignErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | assignErr st₁ st₂ st₃ x₁ x₂ y₁ y₂ e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | assignOk _ _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
    | assignErr _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      rw [h₃] at h₆
      simp at h₆
      obtain ⟨ rfl, rfl ⟩ := h₆
      simp
    | assignErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | assignErrR _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₅
      simp at ih₂
  | assignErrL st x₁ x₂ e h₁ ih =>
    cases h₂ with
    | assignOk _ _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | assignErr _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | assignErrL _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | assignErrR _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | assignErrR st st' x₁ x₂ y₁ e h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | assignOk _ _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | assignErr _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | assignErrL _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | assignErrR _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
  | seqOk st₁ st₂ x₁ x₂ y₁ res h₁ h₂ ih₁ ih₂ =>
    cases h₂ with
    | seqOk _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      exact ih₂
    | seqErr _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
  | seqErr st x₁ x₂ e h₁ ih =>
    cases h₂ with
    | seqOk _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
    | seqErr _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
  | iteThen st st' x₁ x₂ x₃ y₁ res h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | iteThen _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      exact ih₂
    | iteElse _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
    | iteErr₁ _ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | iteErr₂ _ _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
  | iteElse st st' x₁ x₂ x₃ y₁ res h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | iteThen _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
    | iteElse _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₆
      exact ih₂
    | iteErr₁ _ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | iteErr₂ _ _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
  | iteErr₁ st x₁ x₂ x₃ e h₁ ih =>
    cases h₂ with
    | iteThen _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | iteElse _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | iteErr₁ _ _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | iteErr₂ _ _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | iteErr₂ st st' x₁ x₂ x₃ y₁ e h₁ h₂ ih₁ =>
    cases h₂ with
    | iteThen _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | iteElse _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | iteErr₁ _ _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | iteErr₂ _ _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      rw [h₂] at h₄
      simp at h₄
      rw [h₄]
  | loopCont st₁ st₂ st₃ x₁ x₂ y₁ y₂ res h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | loopCont _ _ _ _ _ _ _ _ h₅ h₆ h₇ h₈ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₆
      specialize ih₂ _ h₇
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      specialize ih₃ _ h₈
      exact ih₃
    | loopStop _ _ _ _ _ h₅ h₆ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₆
    | loopErr _ _ _ _ _ _ h₅ h₆ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₆
    | loopErrL _ _ _ _ h₅ =>
      specialize ih₁ _ h₅
      simp at ih₁
    | loopErrR _ _ _ _ _ _ h₅ h₆ h₇ =>
      specialize ih₁ _ h₅
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₆
      specialize ih₂ _ h₇
      simp at ih₂
  | loopStop st st' x₁ x₂ y₁ h₁ h₂ ih₁ =>
    cases h₂ with
    | loopCont _ _ _ _ _ _ _ _ h₃ h₄ h₅ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | loopStop _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
      simp
    | loopErr _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | loopErrL _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | loopErrR _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
  | loopErr st st' x₁ x₂ y₁ e h₁ h₂ ih₁ =>
    cases h₂ with
    | loopCont _ _ _ _ _ _ _ _ h₃ h₄ h₅ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | loopStop _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
    | loopErr _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
      rw [h₄]
    | loopErrL _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | loopErrR _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₄
  | loopErrL st x₁ x₂ e h₁ ih =>
    cases h₂ with
    | loopCont _ _ _ _ _ _ _ _ h₃ _ _ _ =>
      specialize ih _ h₃
      simp at ih
    | loopStop _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
    | loopErr _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
    | loopErrL _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | loopErrR _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
  | loopErrR st st' x₁ x₂ y₁ e h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | loopCont _ _ _ _ _ _ _ _ h₄ h₅ h₆ h₇ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
      specialize ih₂ _ h₆
      simp at ih₂
    | loopStop _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
    | loopErr _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
    | loopErrL _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | loopErrR _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      simp [h₂] at h₅
      specialize ih₂ _ h₆
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
  | caseOk st st' x₁ bs y₁ env x₂ res h₁ h₂ h₃ ih₁ ih₂ =>
    cases h₂ with
    | caseOk _ _ _ _ _ _ _ _ h₄ h₅ h₆ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      rw [h₂] at h₅
      simp at h₅
      obtain ⟨ rfl, rfl ⟩ := h₅
      specialize ih₂ _ h₆
      congr 1
    | caseErr₁ _ _ _ _ h₄ =>
      specialize ih₁ _ h₄
      simp at ih₁
    | caseErr₂ _ _ _ _ _ _ h₄ h₅ =>
      specialize ih₁ _ h₄
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      rw [h₂] at h₅
      simp at h₅
  | caseErr₁ st x₁ bs e h₁ ih =>
    cases h₂ with
    | caseOk _ _ _ _ _ _ _ _ h₃ _ _ =>
      specialize ih _ h₃
      simp at ih
    | caseErr₁ _ _ _ _ h₃ =>
      specialize ih _ h₃
      simp at ih
      simp [ih]
    | caseErr₂ _ _ _ _ _ _ h₃ _ =>
      specialize ih _ h₃
      simp at ih
  | caseErr₂ st st' x₁ bs y₁ e h₁ h₂ ih₁ =>
    cases h₂ with
    | caseOk _ _ _ _ _ _ _ _ h₃ h₄ _ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      rw [h₂] at h₄
      simp at h₄
    | caseErr₁ _ _ _ _ h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | caseErr₂ _ _ _ _ _ _ h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      rw [h₂] at h₄
      simp at h₄
      rw [h₄]
  | scope st x₁ env x₂ res h₁ h₂ ih =>
    cases h₂ with
    | scope _ _ _ _ _ h₃ h₄ =>
      rw [h₁] at h₃
      simp at h₃
      obtain ⟨ rfl, rfl ⟩ := h₃
      specialize ih _ h₄
      congr 1
  | nil st r₂ h₂ => cases h₂; simp
  | cons st₁ st₂ st₃ x xs y ys h₁ h₂ ih₁ ih₂ r₂ h₂ =>
    cases h₂ with
    | cons _ st₂' st₃' _ _ y' ys' h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp
    | err _ st₂' _ _ y' h₂ =>
      specialize ih₁ _ h₂
      simp at ih₁
    | errL _ _ _ e' h₂ =>
      specialize ih₁ _ h₂
      simp at ih₁
    | errR _ st₂' _ _ y' e' h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
  | err st₁ st₂ x xs y h₁ ih r₂ h₂ =>
    cases h₂ with
    | cons _ st₂' st₃' _ _ y' ys' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
    | err _ st₂' _ _ y' h₂ =>
      specialize ih _ h₂
      simp at ih
      obtain ⟨ rfl, rfl ⟩ := ih
      simp
    | errL _ _ _ e' h₂ =>
      specialize ih _ h₂
      simp at ih
    | errR _ st₂' _ _ y' e' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
  | errL st x xs e h₁ ih r₂ h₂ =>
    cases h₂ with
    | cons _ st₂' st₃' _ _ y' ys' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
    | err _ st₂' _ _ y' h₂ =>
      specialize ih _ h₂
      simp at ih
    | errL _ _ _ e' h₂ =>
      specialize ih _ h₂
      simp at ih
      simp [ih]
    | errR _ st₂' _ _ y' e' h₃ h₄ =>
      specialize ih _ h₃
      simp at ih
  | errR st₁ st₂ x xs y e h₁ h₂ ih₁ ih₂ r₂ h₂ =>
    cases h₂ with
    | cons _ st₂' st₃' _ _ y' ys' h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
    | err _ st₂' _ _ y' h₃ =>
      specialize ih₁ _ h₃
      simp at ih₁
    | errL _ _ _ e' h₂ =>
      specialize ih₁ _ h₂
      simp at ih₁
    | errR _ st₂' _ _ y' e' h₃ h₄ =>
      specialize ih₁ _ h₃
      simp at ih₁
      obtain ⟨ rfl, rfl ⟩ := ih₁
      specialize ih₂ _ h₄
      simp at ih₂
      obtain ⟨ rfl, rfl ⟩ := ih₂
      simp

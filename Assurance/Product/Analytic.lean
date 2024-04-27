/-
Copyright (c) 2024 Logan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Logan Murphy
-/
import Assurance.Product.Template
set_option autoImplicit false
open scoped Goal
structure AnalyticTemplate (α X Y: Type) where
 parent : α → Prop
 f : X → Y
 fpred : X → Y →  Prop
 inputRel : α × X → Prop
 inputPred : X → Prop
 outputPred : Y → Prop

namespace AnalyticTemplate

variable {α X Y : Type}

def apply (T : AnalyticTemplate α X Y) : α → X → List Goal := λ a x => [ ∀ x  : X, T.fpred x (T.f x),
      T.inputRel ⬝ (a,x), T.inputPred ⬝ x, T.outputPred ⬝ (T.f x)]

lemma apply_def {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.apply a x = [.atom (∀ x  : X, T.fpred x (T.f x)),
      T.inputRel ⬝ (a,x), T.inputPred ⬝ x, T.outputPred ⬝ (T.f x)] := rfl

def toTemplate  (T : AnalyticTemplate α X Y) : Template α X :=
{ parent := T.parent,
  apply := T.apply}

def prec_trivial {T : AnalyticTemplate α X Y} {a : α} {x : X}  : T.toTemplate.prec a x = True :=
  by rfl

lemma mem_analytic_subgoals_disj  {T : AnalyticTemplate α X Y}  {g : Goal}  {a : α} {x : X} :
  g ∈ (toTemplate T).apply a x ↔ (g = ∀ x  : X, T.fpred x (T.f x)) ∨
  (g = T.inputRel ⬝ (a,x)) ∨  (g = T.inputPred ⬝ x) ∨ (g = T.outputPred ⬝ (T.f x)) :=
    by

      rw [toTemplate] ; simp
      rw [apply_def]
      iterate 4 (rw [List.mem_cons])
      simp_all only [List.not_mem_nil, or_false]

lemma valid_def {T : AnalyticTemplate α X Y} :
  T.toTemplate.valid ↔
    ∀ (a : α) (x : X),
      T.inputRel (a,x) → T.inputPred x → T.outputPred (T.f x) → (∀ k, T.fpred k (T.f k)) → T.parent a :=
by
  rw [Template.valid]
  constructor
  . intros h a x rel inp outp fpred
    replace h := h a x
    rw [prec_trivial] at h ; simp only [forall_true_left] at h
    apply h
    intros g' hg'
    rw [mem_analytic_subgoals_disj] at hg'
    cases' hg' with hg' hg' <;> cases' hg' with hg' hg'
    . rwa [Goal.semantics_atom]
    . rwa [hg', Goal.semantics_pred]
    . cases' hg' with hg' hg' <;> rwa [hg', Goal.semantics_pred]
  . intros h a x prec ; clear prec
    intros subs
    rw [Goal.semantics_pred]
    apply h a x
    apply subs (T.inputRel ⬝ (a,x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (T.inputPred ⬝ x) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (T.outputPred ⬝ (T.f x)) (by rw [mem_analytic_subgoals_disj]; tauto)
    apply subs (∀ k, T.fpred k (T.f k)) (by rw [mem_analytic_subgoals_disj]; tauto)



end AnalyticTemplate

-- import Mathlib
import SPL.Data
import Assurance.ProductLine.vGSN
set_option autoImplicit false
open SPL vSet vGSN

variable {F : Type} [FeatureSet F]
structure vTemplate (A D α γ : Type) (Φ : FeatModel F) [Var α A Φ] [Var γ D Φ] where
  parent : A → Prop
  parentPC : PC F
  apply : α → γ → List (vGoal Φ)
  prec : α → γ → Prop := λ _ _ => True
namespace vTemplate


def valid  {A D α γ : Type} {Φ : FeatModel F} [Var α A Φ] [Var γ D Φ] (T : vTemplate A D α γ Φ) : Prop :=
∀ x d, T.prec x d → refines (vGoal.pred T.parentPC T.parent x) (T.apply x d)

namespace Finite

noncomputable def domainDecomp  {α : Type} [DecidableEq α]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : vTemplate (Finset α) (FinFamily α) (vFinset α F) (vFinFamily α F) Φ :=
  {
    parentPC := pc
    parent := λ s => ∀ x ∈ s, P x
    prec := λ s v => ∀ c : Config Φ, c ⊨ pc → ∀ x ∈ s ↓ c, ∃ T ∈ v ↓ c, x ∈ T
    apply := λ _ v => v.toList.map (λ ⟨s,pc'⟩ => .pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') )
  }

lemma domainDecomp_apply {α : Type} [DecidableEq α] {Φ : FeatModel F} {P : α → Prop} {pc : PC F} {s : vFinset α F} {f : vFinFamily α F} :
  (domainDecomp P pc (Φ:=Φ)).apply s f = f.toList.map (λ ⟨s,pc'⟩ => vGoal.pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') ) :=
  rfl

/- More general (but harder to use) version for general sets below -/
theorem vDomDecompValid {α : Type} [DecidableEq α]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : valid (domainDecomp P pc (Φ:=Φ)) :=
by
  intros s f complete c hsat subs
  rw [domainDecomp_apply] at subs
  rw [domainDecomp,vGoal.pc] at * ;
  simp only [set_idx, Subtype.forall, Prod.mk.eta, List.mem_map,Finset.mem_toList, Prod.exists, forall_exists_index, and_imp] at *
  replace complete := complete c.1 c.2 hsat
  simp only [Subtype.coe_eta] at complete
  rw [semantics,vGoal.derive_pred]
  simp only [set_idx]
  intros k hsatx
  rcases complete k hsatx with ⟨T, hT, hT'⟩
  have := vFinFamily.derive_mem_iff.mp hT
  cases' this with t ht
  replace subs := subs (vGoal.pred t.2 (λ t => ∀ x ∈ t, P x) t) t.1 t.2 (by simp [ht.1] )
  rw [vGoal.pc] at subs ; simp at subs
  replace subs := subs ht.2.2
  rw [semantics, vGoal.derive_pred] at subs
  simp at subs
  apply subs k
  rw [← ht.2.1] at hT'
  rw [derive_def_prod_fin]
  simp [ht.2.2]
  exact hT'

end Finite

variable {α : Type} [DecidableEq α]  {Φ : FeatModel F}

def complete (S : vFinset α F) (V : vFinFamily α F) (Φ : FeatModel F) : Prop :=
  ∀ c : Config Φ,
    ∀ x ∈ S ↓ c,
      ∃ T ∈ V ↓ c, x ∈ T

def decompose (S : vFinset α F) : vFinFamily α F :=
  S.image (λ ⟨a,pc⟩ => ⟨{a},pc⟩)

def explode (S : vFinset α F) : vFinset (Finset α) F :=  S.image (λ ⟨a,pc⟩ => ⟨{a},pc⟩)

 def allPCs (S : vFinset α F) : Finset (PC F) :=
  (explode S).image Prod.snd

 def aggregate
  (S : vFinset α F) : vFinset (Finset α) F :=
  let get_singletons : PC F → (Finset (Finset α)) := λ p => ((explode S).filter <| λ ⟨_,pc⟩ => p = pc).image (Prod.fst)
  let aggregate : PC F → (Finset α) := λ p => (get_singletons p).sup id
  (allPCs S).image (λ pc => ⟨aggregate pc,pc⟩)


theorem complete_decomp {S : vFinset α F} : complete S (explode S) Φ :=
by
  rw [complete]
  rw [explode]
  simp
  intros c hc x xmem
  have := vFinset.derive_mem_iff_exist_pc.mp xmem
  use {x}
  simp only [Finset.mem_singleton, and_true]
  refine vFinset.derive_mem_iff_exist_pc.mpr ?h.a
  simp only [Finset.mem_image, Prod.mk.injEq, Finset.singleton_inj, Prod.exists,
    exists_eq_right_right, exists_eq_right]
  exact this

theorem complete_aggregate [DecidableEq α] {S :vFinset α F} : complete S (aggregate S) Φ :=
by
  rw [complete]
  rw [aggregate]
  simp
  intros c hc x hx
  have := Iff.mp <| vFinset.derive_mem_iff_exist_pc (F := F) (α := α) (c:=⟨c,hc⟩) (x:=x) (S:=S)
  replace this := this hx
  cases' this with p hp
  use (S.image Prod.fst).filter (λ c => ∃ k ∈ S, k.1 = c ∧ k.2 = p)
  simp only [Prod.exists, exists_eq_right_right, exists_eq_right, Finset.mem_filter,
    Finset.mem_image, exists_and_right]
  split_ands
  . rw [vFinset.derive_mem_iff_exist_pc]
    use p
    simp
    split_ands
    . rw [allPCs] ; rw [Finset.mem_image] ; rw [explode] ; simp ;use {x} ; use x ; tauto
    . ext k
      rw [Finset.mem_sup,explode,Finset.mem_filter]; simp ; tauto
    . exact hp.2
  . use p ; exact hp.1
  . exact hp.1






namespace General
/-- NOTE: `[DecidableEq (Set α)]` is not generally synthesizable in practice.
 -- The "easier to use" version is the one for Finsets above.
 -- We keep this version just for reference, while we develop an alternative setup for sets defined  by decidable predicates -/
noncomputable def domainDecomp  {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : vTemplate (Set α) (Family α) (vSet α F) (vFamily α F) Φ :=
  {
    parentPC := pc
    parent := λ s => ∀ x ∈ s, P x
    prec := λ s v => ∀ c : Config Φ, c ⊨ pc → ∀ x ∈ s ↓ c, ∃ T ∈ v ↓ c, x ∈ T
    apply := λ _ v => v.toList.map (λ ⟨s,pc'⟩ => .pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') )
  }

lemma domainDecomp_apply {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} {P : α → Prop} {pc : PC F} {s : vSet α F} {f : vFamily α F} :
  (domainDecomp P pc (Φ:=Φ)).apply s f = f.toList.map (λ ⟨s,pc'⟩ => vGoal.pred pc' (λ t => ∀ x ∈ t, P x) (Prod.mk s pc') ) :=
  rfl

theorem domainDecompValid {α : Type} [DecidableEq (Set α)]  {Φ : FeatModel F} (P : α → Prop) (pc : PC F) : valid (domainDecomp P pc (Φ:=Φ)) :=
by
  intros s f complete c hsat subs
  rw [domainDecomp_apply] at subs
  rw [domainDecomp,vGoal.pc] at * ;
  simp only [set_idx, Subtype.forall, Prod.mk.eta, List.mem_map,Finset.mem_toList, Prod.exists, forall_exists_index, and_imp] at *
  replace complete := complete c.1 c.2 hsat
  simp only [Subtype.coe_eta] at complete
  rw [semantics,vGoal.derive_pred]
  simp only [set_idx]
  intros k hsatx
  rcases complete k hsatx with ⟨T, hT, hT'⟩
  have := vFamily.derive_mem_iff.mp hT
  cases' this with t ht
  replace subs := subs (vGoal.pred t.2 (λ t => ∀ x ∈ t, P x) t) t.1 t.2 (by simp [ht.1] )
  rw [vGoal.pc] at subs ; simp at subs
  replace subs := subs ht.2.2
  rw [semantics, vGoal.derive_pred] at subs
  simp at subs
  apply subs k
  rw [← ht.2.1] at hT'
  rw [derive_def_prod]
  simp [ht.2.2]
  exact hT'

end General
end vTemplate

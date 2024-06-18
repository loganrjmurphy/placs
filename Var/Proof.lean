import Var.Class

universe u v
variable {A : Type u} {α : Type v} {F : Type} [FeatureSet F]

def confInv (Φ : FeatModel F) (φ : FeatExpr F) [Var α A Φ] (P : A → Prop) (x : α) : Prop :=
  ∀ c : Config Φ, c ⊨ φ → P (x ↓ c)

notation "["Φ"| "φ"] "  => confInv Φ φ
notation "["Φ"] " => confInv Φ ⊤


variable {Φ : FeatModel F} {φ : FeatExpr F} [Var α A Φ] {P : A → Prop} {x : α}

theorem varProof_invariant_fm :
  [Φ] P x ↔ ∀ c : Config Φ, P (x ↓ c) :=
    by rw [confInv]
       simp only [Config.sat_univ, true_implies]


theorem varProof_restrict :
  [Φ|φ] P x ↔ ∀ c : Config Φ, c ⊨ φ →  P (x ↓ c) :=
by rfl


theorem varProof_subsume {φ ψ : FeatExpr F} {hsub : ⦃ψ⦄ ⊆ ⦃φ⦄} :
  [Φ|φ] P x → [Φ|ψ] P x :=
by
  intros π c hc
  exact π c (hsub hc)

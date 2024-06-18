import Var.Feature

universe u v

variable {F : Type} [FeatureSet F]
class Var (α  : Type u) (A : outParam  (Type v)) (Φ : FeatModel F) where
  derive : α  → Config Φ → A

infix:80  "↓"  => Var.derive


instance {Φ : FeatModel F} [Var α A Φ] [Var β B Φ] : Var (α × β) (A × B) Φ :=
  ⟨λ (a,b) c => (a ↓ c, b ↓ c)⟩

lemma prod_derive_def {Φ : FeatModel F} [Var α A Φ] [Var β B Φ] {x : α × β} {c : Config Φ} :
x ↓ c = (x.fst ↓ c, x.snd ↓ c) := rfl

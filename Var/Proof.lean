import Var.Class

variable {A α F : Type} [FeatureSet F]

def confInv (Φ : FeatModel F) [Var α A Φ] (P : A → Prop) (x : α) : Prop :=
  ∀ c : Config Φ, P (x ↓ c)

notation "["Φ"] " P "(" x ")" => confInv Φ P x

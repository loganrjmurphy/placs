import Var
import Assurance.Product.GSN
set_option autoImplicit false

variable {F : Type} [FeatureSet F]

inductive vGoal (Φ : FeatModel F)
| atom (pc : PC F) (p : Prop) : vGoal Φ
| pred {A α : Type} [Var α A Φ] (pc : PC F)  (P : A → Prop) (x : α) : vGoal Φ

variable {Φ : FeatModel F}

namespace vGoal

def pc : vGoal Φ → PC F
| vGoal.atom pc _ => pc
| vGoal.pred pc _ _ => pc

def vSemantics : vGoal Φ → Config Φ → Prop
| vGoal.atom _ p => λ _ => p
| vGoal.pred _ P x => λ c => P (x ↓ c)

def asGoal : vGoal Φ → Config Φ → Goal
| vGoal.atom _ p => λ _ => .atom p
| vGoal.pred _ P x => λ c => .pred P (x ↓ c)

instance : Var (vGoal Φ) Goal Φ := ⟨asGoal⟩

lemma derive_atom {A α : Type} [Var α A Φ] {pc : PC F}  {P : Prop}  {c : Config Φ} :
  vGoal.atom (Φ:=Φ) pc P ↓ c = Goal.atom P := rfl

lemma derive_pred {A α : Type} [Var α A Φ] {pc : PC F}  {P : A → Prop} {x : α} {c : Config Φ} :
  vGoal.pred (Φ:=Φ) pc P x ↓ c = Goal.pred P (x ↓ c) := rfl

def varProof : vGoal Φ → Prop := λ g =>
  [Φ| g.pc] Goal.semantics g

end vGoal

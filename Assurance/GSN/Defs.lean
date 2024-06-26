import Mathlib
set_option autoImplicit false

inductive Goal
| atom (p : Prop) : Goal
| pred {α : Type} (P : α → Prop) (x : α) : Goal

instance : Coe Prop Goal := ⟨Goal.atom⟩

namespace Goal

def semantics : Goal → Prop
| .atom p => p
| .pred P x => P x

notation "⟦"G"⟧" => semantics G

end Goal

inductive GSN
| nil : GSN
| evd : Π g : Goal, ⟦g⟧ → GSN
| strategy : Goal → List GSN → GSN

namespace GSN

universe u

instance {G : GSN} : Decidable (G = .nil) :=
  match G with
  | nil => Decidable.isTrue rfl
  | evd _ _ => Decidable.isFalse (nofun)
  | strategy _ _ => Decidable.isFalse (nofun)

@[induction_eliminator]
def inductionOn
  (motive : GSN → Prop)
  (nil : motive nil)
  (evd : ∀ (g : Goal) (e : ⟦g⟧), motive (GSN.evd g e))
  (strategy :
     ∀ (g : Goal) (children : List GSN),
         (∀ (g : GSN), g ∈ children → motive g)
            → motive (GSN.strategy g children))
  : ∀ G : GSN, motive G :=
    @GSN.rec motive (λ gs => ∀ g ∈ gs, motive g) nil evd strategy
    (List.forall_iff_forall_mem.mp trivial)
    (λ x xs hx ih => by simp only at *; exact List.forall_mem_cons.mpr ⟨hx, ih⟩)


@[reducible]
def root? : GSN → Option Goal
| .nil => none
| .evd g _ => g
| .strategy g _ => g

def root : Π (G : GSN), (_ :G ≠ .nil) → Goal
| .nil, h => False.elim <| h rfl
| .evd g _, _ => g
| .strategy g _, _ => g

def roots (l : List GSN) : List Goal := l.map root? |> List.reduceOption

def undevGoals : List Goal → List GSN :=
  List.map (GSN.strategy . [])

@[reducible]
def supported : GSN → Bool
| .nil => False
| .evd _ _ => True
| .strategy _ [] => False
| .strategy _ (h::t) => (h::t).attach.all (λ ⟨x,_ ⟩ => supported x)

def refines (strat : Goal × List GSN) : Prop :=
  let children := roots strat.snd
  (∀ g' ∈ children, ⟦g'⟧) → ⟦strat.fst⟧


def deductive : GSN → Prop
| .nil => False
| .evd _ _ => True
| .strategy g children => refines (g, children) ∧ children.attach.Forall (λ ⟨x,_⟩ => deductive x)

end GSN

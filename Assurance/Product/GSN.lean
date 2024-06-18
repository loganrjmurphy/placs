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

lemma semantics_atom {p : Prop} : semantics p = p := rfl
lemma semantics_pred {α : Type} {P : α → Prop} {x : α} : semantics (.pred P x) = P x := rfl

scoped infix:81 "⬝" => Goal.pred

end Goal


inductive GSN
| nil : GSN
| evd : Π g : Goal, ⟦g⟧ → GSN
| strategy : Goal → List GSN → GSN


namespace GSN
scoped infix:80 "⇐" => GSN.strategy
scoped infix:80 "↼" => GSN.evd

universe u

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
def nnil : GSN → Bool
| .nil => false
| .evd _ _ => true
| .strategy _ _ => true

lemma nnil_def_true {A : GSN} : A.nnil = true ↔ A ≠ GSN.nil := by cases A <;> simp
lemma nnil_def_false {A : GSN} : A.nnil =false ↔ A = GSN.nil := by cases A <;> simp

def root? : GSN → Option Goal
| .nil => none
| .evd g _ => g
| .strategy g _ => g

def root : Π (G : GSN), G.nnil → Goal
| .nil, h => False.elim <| by rw [nnil] at h ; simp at h
| .evd g _, _ => g
| .strategy g _, _ => g

def root_evd {g : Goal} {h : ⟦g⟧} : root (g ↼ h) (by rfl) = g := rfl
def root_decomp {g : Goal} {l : List GSN} : root (g ⇐ l) (by rfl) = g := rfl

lemma root_option_elim {G : GSN} {g : Goal} : G.root? = some g ↔ (∃ h : G.nnil, G.root h = g) :=
  by cases G with
     | nil => simp only [GSN.root?,ne_eq, not_true_eq_false, IsEmpty.exists_iff]
     | evd _ _ => simp only [GSN.root?,Option.some.injEq, ne_eq, not_false_eq_true,exists_true_left,GSN.root]
     | strategy g gs => simp only [GSN.root?, Option.some.injEq, ne_eq, not_false_eq_true,exists_const,GSN.root]

@[reducible]
def supported : GSN → Bool
| .nil => False
| .evd _ _ => True
| .strategy _ [] => False
| .strategy _ (h::t) => (h::t).attach.all (λ ⟨x,_ ⟩ => supported x)

lemma supported_nil : supported .nil = false := rfl
lemma supported_evd {g : Goal} {h : ⟦g⟧} : supported (.evd g h) = true := by rw [supported]; trivial
lemma supported_empty {g : Goal}  : supported (.strategy g []) = false := rfl
lemma supported_cons {g : Goal} {l : List GSN} : supported (.strategy g l) ↔ l ≠ [] ∧ ∀ x ∈ l, supported x :=
  by cases l <;> rw [supported] <;> simp


def roots (l : List GSN) : List Goal := l.map GSN.root? |> List.reduceOption

lemma not_mem_roots_nil {g: Goal} : ¬ (g ∈ roots []) := by rw [roots]; simp only [List.map_nil, List.reduceOption_nil, List.not_mem_nil, not_false_eq_true]
lemma mem_roots_cons {g : Goal} {x : GSN} {xs : List GSN} : g ∈ roots (x::xs) ↔ (∃ h : x.nnil, x.root h = g) ∨ ∃ (x' : GSN) (h' : x'.nnil), x' ∈ xs ∧  x'.root h' = g :=
  by
  rw [roots,List.reduceOption_mem_iff]; simp only [List.map_cons, List.mem_cons, List.mem_map]
  rw [← root_option_elim]
  constructor
  . intro h
    cases h with
    | inl h => left ; symm at h; exact h
    | inr h => right ; rcases h with ⟨w, hw1,hw2⟩; use w; simp only [true_and, hw1]; rwa [root_option_elim] at hw2
  . intro h
    cases h with
    | inl h => left ; symm at h ; exact h
    | inr h => right ; rcases h with ⟨w, hw1,⟨hw2,hw3⟩⟩; use w ; rw [root_option_elim]; simp_all only [true_and, hw3, exists_const]

def refines (strat : Goal × List Goal) : Prop := (∀ g' ∈ strat.snd, ⟦g'⟧) → ⟦strat.fst⟧

@[reducible]
def deductive : GSN → Prop
| .nil => False
| .evd _ _ => True
| .strategy g children => refines (g, (roots children)) ∧ children.attach.Forall (λ ⟨x,_⟩ => deductive x)

lemma not_deductive_nil : ¬ GSN.nil.deductive  := λ h => False.elim h
lemma deductive_evd {g : Goal} {h : ⟦g⟧} : (g ↼ h).deductive := by rw [deductive]; trivial

lemma deductive_evd_eq {g : Goal} {h : ⟦g⟧} : (g ↼ h).deductive = True := by rw [deductive]

lemma deductive_decomp {g : Goal} {l : List GSN}  : (g ⇐ l).deductive ↔ refines (g, (roots l)) ∧ ∀ x ∈ l, deductive x :=
  by rw [deductive, List.forall_iff_forall_mem]
     simp only [List.mem_attach, forall_true_left, Subtype.forall]

lemma supported_nnil {A : GSN} : supported A → A.nnil :=
by intros ; cases A with | nil =>  contradiction | _=> simp only [ne_eq, not_false_eq_true]


theorem proof_of_root : ∀ A : GSN, (h : supported A) → deductive A → ⟦A.root (supported_nnil h)⟧ :=
by
  intros A
  induction A with
  | nil => intros ; contradiction
  | evd _ _ => intros ; rwa [GSN.root]
  | strategy g children ih =>
    intros support deduct
    cases children with
    | nil => contradiction
    | cons x xs =>
      rw [GSN.supported_cons] at support ; rw [GSN.root_decomp] ; rw [deductive_decomp] at deduct
      cases' deduct with refinement children_deductive
      apply refinement
      intros g' hg'; rw [mem_roots_cons] at hg'
      cases hg' with
      | inl h =>
        cases' h with h h' ; rw [←h']
        have mem : x ∈ x::xs := List.Mem.head xs
        exact ih x mem (support.2 x mem) (children_deductive x mem)
      | inr h =>
        rcases h with ⟨x',h,xmem,h''⟩ ; rw [← h'']
        have mem : x' ∈ x::xs := List.mem_cons_of_mem x xmem
        exact ih x' mem (support.2 x' mem) (children_deductive x' mem)

end GSN

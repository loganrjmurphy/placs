import Assurance.Product.Goal

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

@[simp]
lemma evd_root {g : Goal} {h : ⟦g⟧} : root (.evd g h) nofun = g := rfl

@[simp]
lemma strategy_root {g : Goal} {l : List GSN} : root (.strategy g l) (nofun) = g := rfl

@[simp]
lemma root_none_iff {G : GSN} : G.root? = none ↔ G = .nil := by
  cases G <;> simp only

lemma root_some_iff_exists (G : GSN) : (∃ g :  Goal, some g = G.root?) ↔ G ≠ .nil := by
  have := Iff.not <| root_none_iff (G := G)
  rwa [← ne_eq, Option.ne_none_iff_exists] at this

lemma ne_nil_of_some_root {G : GSN} {g : Goal} : (G.root? = some g) →  G ≠ .nil := by
  have := root_some_iff_exists G
  intro h ; exact this.mp (Exists.intro g h.symm)

@[simp]
lemma root_opt_elim {G : GSN} {g : Goal} {h : G ≠ nil} : some g = G.root? ↔ G.root h = g :=
by
  rw [root?]
  cases G with
  | nil => exact False.elim (h rfl)
  | _ => rw [Option.some.injEq] ; tauto

def roots (l : List GSN) : List Goal := l.map GSN.root? |> List.reduceOption

lemma not_mem_roots_nil {g: Goal} : ¬ (g ∈ roots []) :=
  by rw [roots,List.reduceOption_mem_iff,List.map_nil] ; exact List.not_mem_nil (some g)

lemma mem_roots_cons {g : Goal} {x : GSN} {xs : List GSN} : g ∈ roots (x::xs) ↔ (∃ h : x ≠ .nil, x.root h = g) ∨ ∃ (x' : GSN) (h' : x' ≠ .nil), x' ∈ xs ∧ x'.root h' = g :=
  by
  rw [roots,List.reduceOption_mem_iff, List.map_cons, List.mem_cons]
  constructor
  . intro h
    cases h with
    | inl h =>
      left
      have := ne_nil_of_some_root h.symm
      rw [root_opt_elim (h := this)] at h ; use this
    | inr h =>
      right
      rw [List.mem_map] at h
      rcases h with ⟨w, hw1, hw2⟩
      have : w ≠ .nil := ne_nil_of_some_root hw2
      use w ; use this
      exact ⟨hw1, root_opt_elim.mp (Eq.symm hw2) ⟩
  .
    intro h
    cases h with
    | inl h =>
      left
      cases' h with w hw
      exact root_opt_elim.mpr hw
    | inr h =>
      right
      rw [List.mem_map]
      rcases h with ⟨w, hw1, ⟨hw2,hw3⟩⟩
      use w
      exact ⟨ hw2, Eq.symm ((root_opt_elim.mpr) hw3)⟩

def undevGoals : List Goal → List GSN :=
  List.map (GSN.strategy . [])

@[simp]
lemma undevGoals_roots_inv (l : List Goal) : GSN.roots (undevGoals l) = l :=
  by
    rw [GSN.roots, undevGoals,List.reduceOption]
    rw [List.map_map, List.filterMap_map, CompTriple.comp_eq]
    induction l with
    | nil => rfl
    | cons h t ih =>
      simpa only [List.filterMap_cons, Function.comp_apply, List.cons.injEq, true_and]

end GSN

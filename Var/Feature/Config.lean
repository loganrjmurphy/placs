import Var.Feature.FeatExpr


/-- A ConfigSpace is a (finite) set of feature configurations -/
abbrev ConfigSpace (F : Type) [FeatureSet F] := Finset <| Finset F

namespace FeatExpr
@[reducible]
def semantics {F: Type} [FeatureSet F]: FeatExpr F → ConfigSpace F
| ⊤ => Finset.univ
| ⊥ => ∅
| .atom f => Finset.univ.filter (f ∈ .)
| .not FeatExpr => (semantics FeatExpr)ᶜ
| .and pc₁ pc₂ => (semantics pc₁) ∩ (semantics pc₂)
| .or pc₁ pc₂ => (semantics pc₁) ∪ (semantics pc₂)

end FeatExpr

notation "⦃" p "⦄" => FeatExpr.semantics p
variable {F : Type} [FeatureSet F]

@[simp]
lemma imp_semantics {p q : FeatExpr F} : ⦃p⇒q⦄ = ⦃p⦄ᶜ ∪ ⦃q⦄ :=
  by rfl

@[simp]
lemma iff_semantics {p q : FeatExpr F} : ⦃p⇔q⦄ = (⦃p ⇒ q⦄) ∩ (⦃q ⇒ p⦄) :=
by rfl


def Config  (Φ : FeatModel F) : Type := { c : Finset F // c ∈ ⦃Φ⦄}

namespace Config

variable {Φ : FeatModel F}

lemma conj_def {p q : FeatExpr F} : ⦃p &&& q⦄ = ⦃p⦄ ∩ ⦃q⦄ :=
  by rw [FeatExpr.semantics]


def sat  (c : Config Φ) (p : FeatExpr F) : Prop := c.val ∈ ⦃p⦄

infix:50 (priority:=high) "⊨" => sat

variable {c : Config Φ} {p : FeatExpr F}

-- @[simp]
theorem sat_def : c ⊨ p ↔ c.val ∈ ⦃p⦄ := Iff.rfl


lemma sat_univ {c : Config Φ}:  c ⊨ ⊤ :=
  by rw [sat_def,FeatExpr.semantics]; apply Finset.mem_univ

lemma sat_none {c : Config Φ}:  c ⊨ .none → False  :=
  by intro h ; rw [sat_def, FeatExpr.semantics] at h; exact Finset.not_mem_empty c.val h

lemma sat_atom {c : Config Φ} {f : F}  : c ⊨ f ↔ f ∈ c.val :=
  by rw [sat_def, FeatExpr.semantics, Finset.mem_filter,eq_true <| Finset.mem_univ c.val, true_and]

lemma sat_not  {c : Config Φ} {p : FeatExpr F} : c ⊨ ~~~ p ↔ ¬ c ⊨ p :=
  by rw [sat_def, sat_def,
  FeatExpr.semantics,Finset.mem_compl]

lemma sat_conj {c : Config Φ} {p q : FeatExpr F} : c ⊨ p &&& q ↔ c ⊨ p ∧ c ⊨ q :=
  by iterate 3 (rw [sat_def])
     rw [FeatExpr.semantics, Finset.mem_inter]

lemma sat_disj {c : Config Φ} {p q : FeatExpr F} : c ⊨ p ||| q ↔ c ⊨ p ∨ c ⊨ q :=
  by iterate 3 (rw [sat_def])
     rw [FeatExpr.semantics, Finset.mem_union]

lemma sat_imp {c : Config Φ} {p q : FeatExpr F} : c ⊨ p ⇒ q ↔ (c ⊨ p →  c ⊨ q) :=
  by iterate 3 (rw [sat_def])
     rw [imp_semantics, imp_iff_not_or, Finset.mem_union, Finset.mem_compl]

lemma sat_iff  {c : Config Φ} {p q : FeatExpr F} : c ⊨ p ⇔ q ↔ (c ⊨ p ↔ c ⊨ q) :=
  by rw (config := {occs := .pos [2]}) [iff_def]
     iterate 2 (rw [imp_iff_not_or])
     rw [sat_def, sat_def, sat_def, iff_semantics, imp_semantics, imp_semantics]
     rw [Finset.mem_inter,Finset.mem_union,Finset.mem_compl, Finset.mem_union, Finset.mem_compl]


instance {c : Config Φ} {p : FeatExpr F} : Decidable (c ⊨ p) := by apply Finset.decidableMem

end Config

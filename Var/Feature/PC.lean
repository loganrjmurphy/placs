import Var.Feature.Config

/- A presence condition is a feature expression describing a set of valid configurations with respect to some feature model -/
-- structure PC {F : Type} [FeatureSet F] (Φ : FeatModel F) where
--   featExpr    : FeatExpr F
--   satFM : ⦃featExpr⦄ ⊆ ⦃Φ⦄

-- namespace PC

-- variable {F : Type} [FeatureSet F] {Φ : FeatModel F}

-- def sat (c : Config Φ) (pc : PC Φ) : Prop := c ⊨ pc.featExpr

-- instance : CoeOut (PC Φ) (FeatExpr F) := ⟨PC.featExpr⟩

-- instance : OrOp (PC Φ) :=
--   { or :=
--     λ ⟨p, hp⟩ ⟨q, hq⟩ =>
--       {featExpr := p ||| q, satFM := Finset.union_subset hp hq}
--       }


-- instance : AndOp (PC Φ) :=
--   { and :=
--     λ ⟨p, hp⟩ ⟨q, _⟩ =>
--       {featExpr := p &&& q, satFM := by
--         intros c hc
--         rw [Config.conj_def,Finset.mem_inter] at hc
--         cases' hc with hcp hcq
--         apply hp hcp }
--       }


-- end PC

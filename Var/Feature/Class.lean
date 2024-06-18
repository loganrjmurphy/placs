import Mathlib.Data.Fintype.Powerset
/-
A type `F` is a `FeatureSet` if it is finite and has decidable equality
We say that terms of type `F` are "features".
-/
class FeatureSet (α: Type) extends Fintype α where
  dec: DecidableEq α

instance {F : Type} [FeatureSet F] :  DecidableEq F := FeatureSet.dec

instance {n : ℕ} : FeatureSet (Fin n) := .mk inferInstance

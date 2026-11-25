module

public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusBoundsOfConsecutiveRatioBounds
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (r1 r2 : Fin m → kˣ), ∃ R1 R2 : kˣ, ∀ t : Fin (m + 1) → kˣ, t (Fin.last m) = 1 → (∀ i : Fin m, valuation k (r2 i : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) ∧ valuation k ((t i.castSucc : k) / t i.succ) ≤ valuation k (r1 i : k)) → ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k) := by
  first | exact @GlobalTheory.chain_bound | exact GlobalTheory.chain_bound | (intros; apply GlobalTheory.chain_bound <;> assumption)

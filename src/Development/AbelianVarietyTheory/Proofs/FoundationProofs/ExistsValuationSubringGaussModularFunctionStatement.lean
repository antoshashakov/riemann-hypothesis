module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_valuationSubring_gauss_modularFunction : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (q : ℕ), q.Prime → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∃ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval X.jK P) = 1) ∧ ∀ f : X.K, (∀ r, (X.exp f).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp f).coeff r ∈ V.nonunits) → W.valuation (f - algebraMap Ω X.K ((X.exp f).coeff 0)) < 1 := by
  first | exact @GlobalTheory.KZ.exists_valuationSubring_gauss | exact GlobalTheory.KZ.exists_valuationSubring_gauss | (intros; apply GlobalTheory.KZ.exists_valuationSubring_gauss <;> assumption)

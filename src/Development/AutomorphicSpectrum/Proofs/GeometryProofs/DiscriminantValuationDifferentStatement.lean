module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantValuationDifferent
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.discriminant_valuation_different : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)), P.IsPrime → (p : 𝓞 E) ∈ P → ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P = (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | exact GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq | (intros; apply GlobalTheory.CompanionTheory.Different.padicValInt_discr_mul_count_eq <;> assumption)

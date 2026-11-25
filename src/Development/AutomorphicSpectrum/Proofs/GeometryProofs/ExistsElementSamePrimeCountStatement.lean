module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsElementSamePrimeCount
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

theorem _root_.GlobalTheory.T.exists_element_same_prime_count : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ → ∃ x ∈ I, x ≠ 0 ∧ (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | exact GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.exists_mem_count_normalizedFactors_span_eq <;> assumption)

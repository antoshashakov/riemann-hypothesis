module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DifferentDvdRamifiedPrimePower
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.different_dvd_ramified_prime_power : ∀ (E : Type) [Field E] [NumberField E] (t : ℕ), t ≠ 0 → (∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P) → differentIdeal ℤ (𝓞 E) ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by
  first | exact @GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | exact GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow | (intros; apply GlobalTheory.CompanionTheory.Glob.differentIdeal_dvd_span_pow <;> assumption)

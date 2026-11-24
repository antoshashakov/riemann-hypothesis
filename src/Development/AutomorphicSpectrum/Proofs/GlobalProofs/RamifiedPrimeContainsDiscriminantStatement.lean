module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RamifiedPrimeContainsDiscriminant
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.ramified_prime_contains_discriminant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | exact GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal | (intros; apply GlobalTheory.CompanionTheory.GlobalFiniteness.natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal <;> assumption)

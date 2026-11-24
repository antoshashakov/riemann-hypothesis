module

public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingEquivCyclotomicCharacter
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Mathlib.RepresentationTheory.Basic

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.ring_equiv_cyclotomic_character : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (σ : G F Ω), cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | exact GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic | (intros; apply GlobalTheory.CompanionTheory.PTIso.cycMod_intrinsic <;> assumption)

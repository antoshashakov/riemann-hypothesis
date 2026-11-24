module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotallyComplexOfRingEquiv
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Formalism.ConjugateSelfDual.Statement
import Mathlib.RepresentationTheory.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

theorem _root_.GlobalTheory.T.totally_complex_of_ring_equiv : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), IsTotallyComplex F → IsTotallyComplex F' := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.isTotallyComplex_of_ringEquiv <;> assumption)

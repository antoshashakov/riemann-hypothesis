module

public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalGeneratorsBaseChange
import Supplements.MathlibImports.AnalysisAndTactics
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

theorem _root_.GlobalTheory.T.minimal_generators_base_change : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Type) [CommRing S] (c : R →+* S), c.Flat →
    ∀ (r : ℕ) (t : Fin r → R) (I : Ideal R), Ideal.span (Set.range t) = I →
      (∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I →
        ∀ i, x i ∈ IsLocalRing.maximalIdeal R) →
      ∀ y : Fin r → S, ∑ i, c (t i) * y i ∈ (IsLocalRing.maximalIdeal R * I).map c →
        ∀ i, y i ∈ (IsLocalRing.maximalIdeal R).map c := by
  first | exact @GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent | exact GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent | (intros; apply GlobalTheory.CompanionTheory.FewEq.minimal_generators_flat_independent <;> assumption)
